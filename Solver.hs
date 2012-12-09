{-# LANGUAGE 
 FlexibleContexts,  
 FlexibleInstances,
 TupleSections
 #-}
module Solver where

import Unifier
import AST
import Choice
import Control.Monad (void)
import Control.Applicative ((<|>), empty)
import Control.Monad.Error (ErrorT, throwError, runErrorT, lift, unless, when)
import Control.Monad.Error.Class
import Control.Monad.State (StateT, get, put, runStateT, modify)
import Control.Monad.State.Class
import Control.Monad.Writer (WriterT, runWriterT, listens)
import Control.Monad.Writer.Class
import Control.Monad.RWS (RWST, RWS, get, put, tell, runRWST, runRWS, ask)
import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.Trans.Class
import Data.Monoid
import Data.Functor
import Data.Traversable (forM)
import Data.Foldable as F (msum, forM_, fold, Foldable, foldl')
import qualified Data.Map as M
import qualified Data.Set as S

----------------------------------------------------------------------
----------------------- LOGIC ENGINE ---------------------------------
----------------------------------------------------------------------
type Reification = VarGen (Tm,Substitution)
type Deduction = VarGen Substitution

unifier :: [(Name,Tp)] -> Tp -> Reification 
unifier cons t = do
  t' <- case t of
    Atom k -> return k
    _ -> empty
  i <- get
  let isAtom (Atom _) = True
      isAtom _ = False
  msum $ flip map (filter (isAtom . snd) cons) $ \(x,Atom con) -> do
    s <- genUnifyEngine [con :=: t']
    return $ (var x,s) 

left :: Judgement -> Reification
left judge@((x,f):context :|- r) = case f of
  Atom _ -> unifier [(x,f)] r
  Forall nm t1 t2 -> do
    nm' <- getNew
    y <- getNew
    (m,so) <- left $ (y,subst (nm |-> var nm') t2):context :|- r
    let n = case M.lookup nm' so of
          Nothing -> var nm'
          Just a -> a
        s = seq n $ M.delete nm' so
    s' <- natural (subst s $ (x,f):context) $ subst s (n,t1)
    return (subst s' $ subst (y |-> Spine (Var x) [Atom n]) m, s *** s')


right :: Judgement -> Reification
right judge@(context :|- r) = case r of
  Atom _ -> unifier context r
  Forall nm t1 t2 -> do
    nm' <- getNew
    (v,s) <- solve $ (nm', t1):context :|- subst (nm |-> cons nm') t2
    return $ (tpToTm $ Forall nm' t1 (Atom v), s)

solve :: Judgement -> Reification
solve judge@(context :|- r) = right judge <|> (msum $ useSingle (\f ctx -> left $ f:ctx :|- r) context)
  where useSingle f lst = sw id lst
          where sw _ [] = []
                sw placeOnEnd (a:lst) =  f a (placeOnEnd lst):sw (placeOnEnd . (a:)) lst

natural :: [(Name, Tp)] -> (Tm,Tp) -> Deduction
natural cont (tm,ty) = do
  let env = M.fromList cont
  (_, constraints) <- runWriterT $ checkTerm env tm ty
  genUnifyEngine constraints
  

solver :: [(Name,Tp)] -> Tp -> Either String [(Name, Tm)]
solver axioms t = case runError $ runStateT (solve $ axioms :|- t) 0 of
  Right ((tm,s),_) -> Right $ ("query" , varsToCons tm):(recSubst s $ map (\a -> (a,var a)) $ S.toList $ freeVariables t)
    where varsToCons = subst $ M.fromList $ map (\(a,_) -> (a,cons a)) axioms
  Left s -> Left $ "reification not possible: "++s
  
-----------------------------------------------------------------
----------------------- Type Checker ----------------------------    
-----------------------------------------------------------------
type Environment = M.Map Name Tp
type NatDeduct = WriterT [Constraint Tm] (StateT Integer Choice)

checkVariable :: Environment -> Variable -> Tp -> NatDeduct Tp
checkVariable env v t = case v of
  Cons nm -> case env ! nm of
    Nothing -> error $ nm++" was not found in the environment in "++show v
    Just t' -> do
      tell [tpToTm t' :=: tpToTm t]
      return t'
  Var nm -> case env ! nm of
    Nothing -> do 
      (t'',s) <- lift $ solve $ M.toList env :|- t
      tell $ map (\(s,t) -> var s :=: t ) $ M.toList s 
      tell [var nm :=: t'']
      return t
      -- I'm not sure this makes sense at all.
      -- in the mean time, assume there is only one use of each unbound variable
    Just t' -> do
      tell [tpToTm t' :=: tpToTm t]
      return t'
checkTerm :: Environment -> Tm -> Tp -> NatDeduct (Tm,Tp)
checkTerm env v t = case v of
  Spine a l -> do
    nm <- (++'α':show a) <$> getNew
    tv1 <- (++':':show a) <$> getNew
    tv2l <- forM l $ \b -> do
      bty <- getNew
      nm' <- getNew
      t' <- checkTerm env (tpToTm b) $ Atom $ var bty
      return (nm',t')
      
    tv1' <- checkVariable env a $ Atom $ var $ tv1
    
    tell [ tpToTm tv1' :=: tpToTm (foldr (\(nm,b) tp -> Forall nm (snd b) tp) t tv2l ) ]
    return $ (Spine a $ map (Atom . fst . snd) tv2l, t)
        
  Abs nm ty tm -> do
    ty' <- checkTipe env ty
    v1 <- (++':':'<':nm) <$> getNew
    nm' <- (++'@':nm) <$> getNew
    v2 <- (++':':'>':nm) <$> getNew

    tell [ tpToTm (Forall v1 ty $ Atom $ var v2) :=: tpToTm t ]
    
    ((tm',t'),constraints) <- listen $ checkTerm (M.insert nm' ty env) (subst (nm |-> var nm') tm) $ Atom $ var v2
    s <- finishSubstWith nm' <$> (lift $ genUnifyEngine constraints)
    tell $ map (\(s,t) -> var s :=: t ) $ M.toList s
    let s' = s *** nm' |-> var nm 
    return $ (Abs nm ty' $ subst s' tm' , Forall v1 ty t')
    
checkTipe :: Environment -> Tp -> NatDeduct Tp
checkTipe env v = case v of
  Atom tm -> do
    (a,t) <- checkTerm env tm atom
    return $ Atom a
  Forall nm ty t -> do
    ty' <- checkTipe env ty
    nm' <- (++'*':nm) <$> getNew
    (a,constraints) <- listen $ checkTipe (M.insert nm' ty env) $ subst (nm |-> var nm') t
    s <- finishSubstWith nm' <$> (lift $ genUnifyEngine constraints)
    
    tell $ map (\(s,t) -> var s :=: t ) $ M.toList s
    let s' = s *** nm' |-> var nm 
    return $ Forall nm ty' (subst s' a)
    
getCons tm = case tm of
  Spine (Cons t) _ -> return t
  Abs _ _ t -> getCons t
  _ -> throwError $ "can't place a non constructor term here: "++ show tm

getPred tp = case tp of
  Atom t -> getCons t
  Forall _ _ t -> getPred t

-- need to do a topological sort of types and predicates.
-- such that types get minimal correct bindings
checkType :: Environment -> Name -> Tp -> Choice Tp
checkType env base ty = fmap fst $ flip runStateT 0 $ appendErr ("FOR: "++show ty) $ do
  con <- getPred ty
  unless (null base || con == base) 
    $ throwError $ "non local name \""++con++"\" expecting "++base
  (ty',constraints) <- runWriterT $ checkTipe env ty
  
  s <- appendErr ("CONSTRAINTS: "++show constraints) $ genUnifyEngine constraints
  
  return $ subst s ty'

typeCheckPredicate :: Environment -> Predicate -> Choice Predicate
typeCheckPredicate env (Query nm ty) = appendErr ("in query : "++show ty) $ do
  ty' <- checkType env "" ty
  return $ Query nm ty
typeCheckPredicate env pred@(Predicate pnm pty plst) = appendErr ("in\n"++show pred) $ do
  pty' <- appendErr ("in name: "++ pnm ++" : "++show pty) $
    checkType env "atom" pty
  plst' <- forM plst $ \(nm,ty) -> 
    appendErr ("in case: " ++nm ++ " = "++show ty) $ (nm,) <$> checkType env pnm ty
  return $ Predicate pnm pty' plst'

typeCheckAll :: [Predicate] -> Choice [Predicate]
typeCheckAll preds = forM preds $ typeCheckPredicate assumptions
  where assumptions = M.fromList $ 
                      ("atom", atom): -- atom : atom is a given.
                      ("forall", Atom $ Abs "_" (Atom $ Abs "_" atom $ cons "atom") $ cons "atom"): -- atom : atom is a given.
                      concatMap (\st -> case st of
                                    Query _ _ -> []
                                    _ -> (predName st, predType st):predConstructors st) preds
