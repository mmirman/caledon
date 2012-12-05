{-# LANGUAGE 
 FlexibleContexts,  
 FlexibleInstances,
 ScopedTypeVariables,
 MultiParamTypeClasses, 
 UndecidableInstances,
 IncoherentInstances,
 TupleSections
 #-}
module Unifier where

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
import Debug.Trace

--------------------------------------------------------------------
----------------------- UNIFICATION --------------------------------
--------------------------------------------------------------------
type VarGen = StateT Integer Choice


class HasVar a where
  getV :: a -> Integer
  setV :: Integer -> a -> a
instance HasVar Integer where  
  getV = id
  setV a _ = a

getNew :: (MonadState a m, HasVar a) => m Name
getNew = do 
  st <- get
  let n = 1 + getV st
  modify (setV n)
  return $! show n
      
unifyAll env (a:l) = do
  s <- unify env a
  s' <- unifyAll env (subst s l)
  return $ s *** s'

unify :: S.Set Name -> Constraint Tm -> VarGen Substitution
unify env constraint@(a :=: b) = 
  let badConstraint = throwError $ show constraint 
      unify' = unify env
      
      doUntoBoth m n = F.foldl' act return (zip m n) mempty
      act prev (mt,nt) sub = do
              sub' <- unify env $ subst sub (tpToTm mt :=: tpToTm nt)
              return $ sub *** sub'

  in case a :=: b of
    _ :=: _ | a > b -> unify env $ b :=: a
    Abs n ty t :=: Abs n' ty' t' -> do  
      s <- unify' $ tpToTm ty :=: tpToTm ty'
      nm <- getNew
      s' <- unify (S.insert nm env) $ subst (M.insert n (var nm) s) t :=: subst (s *** n' |-> var nm) t'
      return $ s *** M.delete nm s'
    Abs n ty t :=: _ -> do  
      nm <- getNew
      s <- unify (S.insert nm env) $ subst (n |-> var nm) t :=: rebuildSpine b [Atom $ var nm]
      return $ M.delete nm s
    
    Spine (Var a) [] :=: Spine (Var a') [] | a == a' -> 
      return mempty
    Spine (Var a) [] :=: _ | not $ S.member a $ freeVariables b -> 
      return $ a |-> b
    Spine (Var a) l :=: _ -> badConstraint
    
    Spine (Var a) m :=: Spine (Var a') n | a == a' && S.member a env && length m == length n -> 
      doUntoBoth m n
    Spine (Cons c) _ :=: Spine (Cons c') _ | c /= c' -> 
      badConstraint
    Spine (Cons c) m :=: Spine (Cons c') n | length m == length n -> 
      doUntoBoth m n
      
    Spine (Var x) n :=: Spine (Cons c) m | not $ S.member x env -> do -- Gvar-Const
      us <- forM n $ const $ Atom <$> var <$> getNew
      xs <- forM m $ const $ Var <$> getNew
      let l = Spine (Cons c) $ (\xi -> Atom $ Spine xi us) <$> xs
      unify' $ subst (x |-> l) (a :=: b)
      -- I need to keep track of levels in the environment! 
      
    _ :=: _ -> badConstraint
  
{-    Hole :=: _ -> return () -- its a hole, what can we say?
    _ :=: Hole -> =return () -- its a hole, what can we say?
    Var v :=: _ -> case b of
      Var v' | v == v' -> return ()
      _ | S.member v (freeVariables b) -> throwError $ "occurs: " ++ show constraint      
      _ -> case t ! v of 
        Nothing -> v +|-> b
        Just s -> putConstraints [s :=: b]
    Abstract n ty t :=: Abstract n' ty' t' -> do  
      putConstraints [ tpToTm ty :=: tpToTm ty' ]
      nm <- getNew
      putConstraints [ subst (n |-> Var nm) t :=: subst (n' |-> Var nm) t' ]
    Cons nm :=: Cons nm' -> do
      unless (nm == nm') badConstraint 
    App a b :=: App a' b' -> do
      putConstraints [a :=: a', b :=: b']
    TyApp a t :=: TyApp a' t' -> do
      putConstraints [tpToTm t :=: tpToTm t' , a :=: a'] -}

genUnifyEngine consts = do
  s <- unifyAll mempty consts
  return $ M.fromList $ recSubst s $ M.toList s
  
--------------------------------------------------------------------
----------------------- REIFICATION --------------------------------
--------------------------------------------------------------------

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
--    return (subst s' $ subst (y |-> TyApp (Var x) (Atom n)) m, s *** s')
    undefined
  p@(Atom _) :->: b -> do
    y <- getNew
    (m,s)  <- left $ (y,b):context :|- r
    (n,s') <- solve $ subst s $ context :|- p
--    return (subst s' $ subst (y |-> App (Var x) n) m, s *** s')
    undefined
  t1 :->: t2 -> do
    y <- getNew
    (m,s)  <- left $ (y,t2):context :|- r
    (n,s') <- solve $ subst s $ (x,f):context :|- t1
--    return (subst s' $ subst (y |-> App (Var x) n) m, s *** s')
    undefined

right :: Judgement -> Reification
right judge@(context :|- r) = case r of
  Atom _ -> unifier context r
  t1 :->: t2 -> do
    nm <- getNew
    (m,s) <- solve $ (nm,t1):context :|- t2
    --return $ (Abstract nm t1 m, s)
    undefined
  Forall nm t1 t2 -> do
    nm' <- getNew
    (v,s) <- solve $ (nm', t1):context :|- subst (nm |-> cons nm') t2
    --return $ (Cons "forall" .+. Abstract nm' t1 v, s)
    undefined

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
  
----------------------------------------------------------------------
----------------------- LOGIC ENGINE ---------------------------------
----------------------------------------------------------------------
recSubst :: (Eq b, Subst b) => Substitution -> b -> b
recSubst s f = fst $ head $ dropWhile (not . uncurry (==)) $ iterate (\(_,b) -> (b,subst s b)) (f,subst s f)  

solver :: [(Name,Tp)] -> Tp -> Either String [(Name, Tm)]
solver axioms t = case runError $ runStateT (solve $ axioms :|- t) 0 of
  Right ((tm,s),_) -> Right $ ("query" , varsToCons tm):(recSubst s $ map (\a -> (a,var a)) $ S.toList $ freeVariables t)
    where varsToCons = subst $ M.fromList $ map (\(a,_) -> (a,cons a)) axioms
  Left s -> Left $ "reification not possible: "++s
  
-----------------------------------------------------------------
----------------------- Type Checker ----------------------------    
-----------------------------------------------------------------
type Environment = M.Map Name Tp

checkVariable :: Environment -> Variable -> Tp -> WriterT [Constraint Tm] (StateT Integer Choice) ()
checkVariable env v t = case v of
  Cons nm -> case env ! nm of
    Nothing -> error $ nm++" was not found in the environment in "++show v
    Just t' -> tell [tpToTm t' :=: tpToTm t]
  Var nm -> case env ! nm of
    Nothing -> do 
      (t'',s) <- lift $ solve $ M.toList env :|- t
      tell [var nm :=: t'']
      -- I'm not sure this makes sense at all.
      -- in the mean time, assume there is only one use of each unbound variable
    Just t' -> tell [tpToTm t' :=: tpToTm t]
      
checkTerm :: Environment -> Tm -> Tp -> WriterT [Constraint Tm] (StateT Integer Choice) ()
checkTerm env v t = case v of
  Spine a l -> do
    nm <- getNew
    tv1 <- getNew
    tv2l <- mapM (\b -> (,b) <$> Atom <$> var <$> getNew) l
    tell [ Spine (Var tv1) (fst <$> tv2l) :=: tpToTm t]  -- maybe?  tpToTm tv1 will have a forall type, which can't be substituted maybe?
    checkVariable env a $ Atom $ var $ tv1
    forM_ tv2l $ \(tv2,b) -> 
      checkTerm env (tpToTm b) $ tv2
  
  Abs nm ty tm -> do
    v1 <- (++'<':nm) <$> getNew
    v2 <- var <$> (++'>':nm) <$>  getNew
        
    tell [ v2 :=: rebuildSpine (tpToTm t) [Atom $ var v1]]
    
    (_,newconstraints) <- listens id $ checkTerm (M.insert v1 ty env) (subst (nm |-> var v1) tm) $ Atom v2
    s <- lift $ genUnifyEngine newconstraints
    let s' = M.delete v1 s
    tell $ map (\(s,i) -> var s :=: i) $ M.toList s'

getCons tm = case tm of
  Spine (Cons t) _ -> return t
  Abs _ _ t -> getCons t
  _ -> throwError $ "can't place a non constructor term here: "++ show tm

getPred tp = case tp of
  Atom t -> getCons t
  Forall _ _ t -> getPred t
  t1 :->: t2 -> getPred t2
  
-- need to do a topological sort of types and predicates.
-- such that types get minimal correct bindings
checkType :: Environment -> Name -> Tp -> Choice Tp
checkType env base ty = fmap fst $ flip runStateT 0 $ do
  con <- getPred ty
  unless (null base || con == base) 
    $ throwError $ "non local name "++con++" expecting "++base
  (_,constraints) <- runWriterT $ checkTerm env (tpToTm ty) $ Atom $ cons "atom"
  s <- genUnifyEngine constraints
  return $ subst s ty

typeCheckPredicate :: Environment -> Predicate -> Choice Predicate
typeCheckPredicate env (Query nm ty) = appendErr ("in query : "++show ty) $ Query nm <$> checkType env "" ty
typeCheckPredicate env pred@(Predicate pnm pty plst) = appendErr ("in\n"++show pred) $ do
  pty' <- appendErr ("in name: "++ pnm ++" : "++show pty) $
    checkType env "atom" pty
  plst' <- forM plst $ \(nm,ty) -> 
    appendErr ("in case: " ++nm ++ " = "++show ty) $ (nm,) <$> checkType env pnm ty
  return $ Predicate pnm pty' plst'
  
typeCheckAll :: [Predicate] -> Choice [Predicate]
typeCheckAll preds = forM preds $ typeCheckPredicate assumptions
  where atom = Atom $ cons "atom"
        assumptions = M.fromList $ 
                      ("atom", atom): -- atom : atom is a given.
                      ("->", atom :->: atom :->: atom): -- atom : atom is a given.
                      ("forall", (atom :->: atom) :->: atom): -- atom : atom is a given.
                      ("exists", (atom :->: atom) :->: atom): -- atom : atom is a given.
                      concatMap (\st -> case st of
                                    Query _ _ -> []
                                    _ -> (predName st, predType st):predConstructors st) preds
