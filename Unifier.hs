{-# LANGUAGE 
 FlexibleContexts,  
 FlexibleInstances,
 ScopedTypeVariables,
 MultiParamTypeClasses, 
 UndecidableInstances,
 IncoherentInstances
 #-}
module Unifier where

import AST
import Choice
import Control.Monad (void)
import Control.Applicative ((<|>), empty)
import Control.Monad.Error (ErrorT, throwError, runErrorT, lift, unless, when)
import Control.Monad.State (StateT, get, put, runStateT, modify)
import Control.Monad.State.Class
import Control.Monad.Writer.Class
import Control.Monad.RWS (RWST, RWS, get, put, tell, runRWST, runRWS, ask)
import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.Trans.Class
import Data.Monoid
import Data.Functor
import Data.Foldable as F (msum, forM_)
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace

--------------------------------------------------------------------
----------------------- UNIFICATION --------------------------------
--------------------------------------------------------------------
data St = St { substitution :: Substitution
             , constraints :: [Constraint Tm]
             , variable :: Integer 
             } 
          
class ConstraintGen m where
  putConstraints :: [Constraint Tm] -> m ()
instance Monad m => ConstraintGen (StateT St m) where
  putConstraints l = modify $ \s -> s { constraints = l++constraints s }  
instance MonadWriter [Constraint Tm] m => ConstraintGen m where  
  putConstraints = tell

type Unify a = StateT St Choice a

class HasVar a where
  getV :: a -> Integer
  setV :: Integer -> a -> a
instance HasVar Integer where  
  getV = id
  setV a _ = a
instance HasVar St where  
  getV = variable  
  setV a st = st { variable = a}  

getNew :: (MonadState a m, HasVar a) => m Name
getNew = do 
  st <- get
  let n = 1 + getV st
  modify (setV n)
  return $! show n
               
               


(+|->) :: Name -> Tm -> Unify ()
nm +|-> tm = modify $ \st -> st { substitution = M.insert nm tm $ subst (nm |-> tm) $ substitution st }


isValue :: Tm -> Bool
isValue (App (Abstract _ _ _) _) = False
isValue (App t1 t2) = isValue t1 && isValue t2
isValue (TyApp (Abstract _ _ _) _) = False
isValue (TyApp t1 tp) = isValue t1
isValue _ = True


nextConstraint :: ((Substitution, Constraint Tm) -> Unify ()) -> Unify ()
nextConstraint m = do
  st <- get
  case constraints st of
    [] -> return ()
    a:l -> do
      put $ st { constraints = l }
      m (substitution st,a)
      
unify :: Unify ()
unify = nextConstraint $ \(t, constraint@(a :=: b)) -> let
  badConstraint = throwError $ show constraint 
  in case (a :=: b) of
    _ :=: _ | a > b -> putConstraints [b :=: a] >> unify
    Var v :=: _ -> case t ! v of 
      Nothing -> case b of
        Var v' | v == v' -> unify
        _ -> v +|-> b >> unify
      Just s -> putConstraints [s :=: b] >> unify
    Abstract n ty t :=: Abstract n' ty' t' -> do  
      putConstraints [ tpToTm ty :=: tpToTm ty' ]
      nm <- getNew
      putConstraints [ subst (n |-> Var nm) t :=: subst (n' |-> Var nm) t' ]
      unify
    Cons nm :=: Cons nm' -> do
      unless (nm == nm') badConstraint 
      unify
    App a b :=: App a' b' -> do
      putConstraints [a :=: a', b :=: b']
      unify
    TyApp a t :=: TyApp a' t' -> do
      putConstraints [tpToTm t :=: tpToTm t' , a :=: a']
      unify
    _ :=: _ -> badConstraint

unifyEngine consts i = snd <$> runStateT unify (St nil consts i)
--------------------------------------------------------------------
----------------------- REIFICATION --------------------------------
--------------------------------------------------------------------
type Reifier = RWST () Substitution Integer Choice
type Reification = Reifier Substitution                                      

unifier :: [Tp] -> Tp -> Reification 
unifier cons t = do
  t' <- case t of
    Atom _ k -> return k
    _ -> empty
  i <- get
  let isAtom (Atom _ _) = True
      isAtom _ = False
  F.msum $ flip map (filter isAtom cons) $ \(Atom _ con) -> do
    s <- lift $ unifyEngine [con :=: t'] i
    put $ variable s
    tell $ substitution s
    return $ substitution s

isPos t = case t of 
  _ :->: _ -> False
  Atom t _ -> t
  Forall _ _ _ -> False
  _ -> True 

blurL judge@(f:_ :|- _) soln  = if isPos f then solve judge else soln
focusL judge@(f:_ :|- _) soln = if isPos f then soln else leftFocused judge

blurR judge@(_ :|- r) soln = if isPos r then soln else solve judge
focusR judge@(_ :|- r) soln = if isPos r then rightFocused judge else soln

leftFocused :: Judgement -> Reification
leftFocused judge@(f:context :|- r) = blurL judge soln
  where soln = case f of
          Atom False _ -> unifier [f] r
          Forall nm _ t1 -> do
            nm' <- getNew
            s <- leftFocused $ subst (nm |-> Var nm') t1:f:context :|- r
            return $ M.delete nm' s
            
          (c :->: d) :->: b -> do  -- Sketchy
            s  <- rightFocused $ (d:->:b):c:context :|- d
            s' <- leftFocused $ subst s $ b:context :|- r
            return $ s *** s'
          p@(Atom _ l) :->: b -> do  -- Sketchy
            s  <- leftFocused $ b:context :|- r
            s' <- rightFocused $ subst s $ context :|- p
            return $ s *** s'
          t1 :->: t2 -> do
            s  <- rightFocused $ f:context :|- t1 -- could use GIpi but the BFS seems to be good enough.
            s' <- leftFocused $ subst s $ t2:context :|- r
            return $ s *** s'
          _ -> empty

leftUnfocused :: Judgement -> Reification
leftUnfocused judge@(f:context :|- r) = focusL judge soln
  where soln = case f of
          Exists nm _ t2 -> do
            nm' <- getNew
            solve $ (subst (nm |-> Cons nm') t2):context :|- r
          _ -> empty
          
rightFocused :: Judgement -> Reification
rightFocused judge@(context :|- r) = blurR judge soln
  where soln = case r of
          Atom True _ -> unifier context r
          Exists nm _ t1 -> do
            nm' <- getNew
            s <- rightFocused $ context :|- subst (nm |-> Var nm') t1
            return $ M.delete nm' s
          _ -> empty
          
rightUnfocused :: Judgement -> Reification
rightUnfocused judge@(context :|- r) = focusR judge soln
  where soln = case r of
          t1 :->: t2 -> solve $ t1:context :|- t2
          Forall nm _ t2 -> do
            nm' <- getNew
            solve $ context :|- subst (nm |-> Cons nm') t2
          _ -> empty

solve :: Judgement -> Reification
solve judge@(context :|- r) = rightUnfocused judge <|> (F.msum $ useSingle (\f ctx -> leftUnfocused $ f:ctx :|- r) context)
  where useSingle f lst = sw id lst
          where sw _ [] = []
                sw placeOnEnd (a:lst) =  f a (placeOnEnd lst):sw (placeOnEnd . (a:)) lst

----------------------------------------------------------------------
----------------------- LOGIC ENGINE ---------------------------------
----------------------------------------------------------------------
freeVariables (Forall a ty t) = (S.delete a $ freeVariables t) `S.union` (freeVariables ty)
freeVariables (Exists a ty t) = (S.delete a $ freeVariables t) `S.union` (freeVariables ty)
freeVariables (t1 :->: t2) = freeVariables t1 `S.union` freeVariables t2
freeVariables (Atom _ a) = fV a
  where fV (App a b) = fV a `S.union` fV b
        fV (TyApp a b) = fV a `S.union` freeVariables b
        fV (Abstract nm a b) = (S.delete nm $ fV b) `S.union` freeVariables a
        fV (Var a) = S.singleton a
        fV (Cons _) = mempty

solver :: [Tp] -> Tp -> Either String [(Name, Tm)]
solver axioms t = case runError $ runRWST (solve $ axioms :|- t) () 0 of
  Right (_,_,s) -> Right $ recSubst $ map (\a -> (a,Var a)) $ S.toList $ freeVariables t
    where recSubst f = fst $ head $ dropWhile (not . uncurry (==)) $ iterate (\(a,b) -> (b,subst s b)) (f,subst s f)
  Left s -> Left $ "reification not possible: "++s

-----------------------------------------------------------------
----------------------- Type Checker ----------------------------    
-----------------------------------------------------------------
                       
type Environment = M.Map Name Tp
type TypeChecker = RWST Environment [Constraint Tm] Integer Error

tpToTm (Forall n ty t) = Cons "forall" .+. Abstract n ty (tpToTm t)
tpToTm (Exists n ty t) = Cons "exists" .+. Abstract n ty (tpToTm t)
tpToTm (Atom _ tm) = tm
tpToTm (t1 :->: t2) = Cons "->" .+. tpToTm t1 .+. tpToTm t2

checkTerm :: Tm -> Tp -> TypeChecker ()
checkTerm (Cons nm) t' = do
  maybe_tenv <- (! nm) <$> ask
  case maybe_tenv of 
    Nothing -> error $ nm++" was not found in the environment"
    Just t -> tell [tpToTm t :=: tpToTm t']
checkTerm v@(Var nm) t = return ()
checkTerm (TyApp a b) ty2 = do
  nm <- getNew
  v1 <- Atom True <$> Var <$> getNew
  v2 <- Var <$> getNew
  let tm2 = tpToTm ty2
      tmB = tpToTm b
  checkTerm a $ Forall nm v1 (Atom True v2)
  checkTerm tmB v1  
  tell [Var nm :=: tmB]  
  tell [v2 :=: tm2]
  
checkTerm (App a b) t = do
  v1 <- Atom True <$> Var <$> getNew
  v2 <- Var <$> getNew
  tell [v2 :=: tpToTm t]
  checkTerm a $ v1 :->: (Atom True v2)
  checkTerm b $ v1
checkTerm (Abstract nm ty tm) t = do
  v1 <- Var <$> getNew
  v2 <- Atom True <$> Var <$> getNew
  tell [v1 :=: tpToTm ty]
  checkTerm (subst (nm |-> v1) tm) v2
  tell [tpToTm t :=: tpToTm (Atom True v1 :->: v2 )]

getCons tm = case tm of
  Cons t -> return t
  App t1 t2 -> getCons t1
  TyApp t1 t2 -> getCons t1
  _ -> throwError $ "can't place a non constructor term here: "++ show tm
  
checkType :: Environment -> Name -> Tp -> Error ()
checkType env base ty = do
  let checkTp rms t = case t of
          Atom k t -> do 
            when rms $ do
              c <- getCons t
              unless (null base || c == base) $ throwError $ "non local name "++c++" expecting "++base
            checkTerm t $ Atom k $ Cons "atom"
          Exists n ty t -> do
            v1 <- Var <$> getNew
            checkTp False ty
            tell [ tpToTm ty :=: v1 ]
            checkTp rms $ subst (n |-> v1) t -- TODO
          Forall n ty t -> do
            v1 <- Var <$> getNew
            checkTp False ty
            tell [ tpToTm ty :=: v1 ]
            checkTp rms $ subst (n |-> v1) t -- TODO
          t1 :->: t2 -> do 
            checkTp False t1
            checkTp rms t2
  ((),i,constraints) <- runRWST (checkTp True ty) env 0
  case runError $ unifyEngine constraints i of
    Left e  -> throwError $ "UNIFY FAILED: " ++ e
    Right _ -> return ()

typeCheckPredicate :: Environment -> Predicate -> Error ()
typeCheckPredicate env (Query _ ty) = appendErr ("in query : "++ show ty) $ checkType env "" ty
typeCheckPredicate env pred = appendErr ("in\n"++show pred) $ do
  appendErr ("in name: "++ predName pred ++" = "++show (predType pred)) $
    checkType env "atom" (predType pred)
  forM_ (predConstructors pred) $ \(nm,ty) -> 
    appendErr ("in case: " ++nm ++ " = "++show ty) $ checkType env (predName pred) ty
  
typeCheckAll :: [Predicate] -> Error ()
typeCheckAll preds = forM_ preds $ typeCheckPredicate assumptions
  where atom = Atom True $ Cons "atom"
        assumptions = M.fromList $ 
                      ("atom", atom): -- atom : atom is a given.
                      ("->", atom :->: atom :->: atom): -- atom : atom is a given.
                      ("forall", (atom :->: atom) :->: atom): -- atom : atom is a given.
                      ("exists", (atom :->: atom) :->: atom): -- atom : atom is a given.
                      concatMap (\st -> case st of
                                    Query _ _ -> []
                                    _ -> (predName st, predType st):predConstructors st) preds
