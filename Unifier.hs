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
import Control.Monad.State (StateT, get, put, runStateT, modify)
import Control.Monad.State.Class
import Control.Monad.Writer.Class
import Control.Monad.RWS (RWST, RWS, get, put, tell, runRWST, runRWS, ask)
import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.Trans.Class
import Data.Monoid
import Data.Functor
import Data.Traversable (forM)
import Data.Foldable as F (msum, forM_, fold, Foldable)
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


nextConstraint :: ((Substitution, Constraint Tm) -> Unify ()) -> Unify ()
nextConstraint m = do
  st <- get
  case constraints st of
    [] -> return ()
    a:l -> do
      put $ st { constraints = l }
      m (substitution st,a)
      unify
      
unify :: Unify ()
unify = nextConstraint $ \(t, constraint@(a :=: b)) -> let
  badConstraint = throwError $ show constraint 
  in case (a :=: b) of
    Hole :=: _ -> return () -- its a hole, what can we say?
    _ :=: _ | a > b -> putConstraints [b :=: a]
    Var v :=: _ -> case t ! v of 
      Nothing -> case b of
        Var v' | v == v' -> return ()
        _ -> v +|-> b
      Just s | S.member v (freeVariables s) -> badConstraint
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
      putConstraints [tpToTm t :=: tpToTm t' , a :=: a']
    _ :=: _ -> badConstraint

unifyEngine consts i = do
  s <- snd <$> runStateT unify (St nil consts i)
  let sub' = substitution s
      sub = M.fromList $ recSubst sub' (M.toList sub')  
  return $ s { substitution = sub }

--------------------------------------------------------------------
----------------------- REIFICATION --------------------------------
--------------------------------------------------------------------
type Reifier = RWST () Substitution Integer Choice
type Reification = Reifier (Tm,Substitution)
type Deduction = Reifier Substitution

unifier :: [(Name,Tp)] -> Tp -> Reification 
unifier cons t = do
  t' <- case t of
    Atom k -> return k
    _ -> empty
  i <- get
  let isAtom (Atom _) = True
      isAtom _ = False
  msum $ flip map (filter (isAtom . snd) cons) $ \(x,Atom con) -> do
    s <- lift $ unifyEngine [con :=: t'] i
    put $ variable s

    tell $ substitution s
    return $ (Var x,substitution s) 

left :: Judgement -> Reification
left judge@((x,f):context :|- r) = case f of
  Atom _ -> unifier [(x,f)] r
  Forall "" t1 t2 -> left $ (x,t1 :->: t2):context  :|- r
  Forall nm t1 t2 -> do
    nm' <- getNew
    y <- getNew
    (m,so) <- left $ (y,subst (nm |-> Var nm') t2):context :|- r
    let n = case M.lookup nm' so of
          Nothing -> Var nm'
          Just a -> a
        s = seq n $ M.delete nm' so
    s' <- natural (subst s $ (x,f):context) $ subst s (n,t1)
    return (subst s' $ subst (y |-> TyApp (Var x) (Atom n)) m, s *** s')

  p@(Atom _) :->: b -> do
    y <- getNew
    (m,s) <- left $ (y,b):context :|- r
    (n,s') <- solve $ subst s $ context :|- p
    return (subst s' $ subst (y |-> App (Var x) n) m, s *** s')
  t1 :->: t2 -> do
    y <- getNew
    (m,s)  <- left $ (y,t2):context :|- r
    (n,s') <- solve $ subst s $ (x,f):context :|- t1
    return (subst s' $ subst (y |-> App (Var x) n) m, s *** s')

right :: Judgement -> Reification
right judge@(context :|- r) = case r of
  Atom _ -> unifier context r
  t1 :->: t2 -> do
    nm <- getNew
    (m,s) <- solve $ (nm,t1):context :|- t2
    return $ (Abstract nm t1 m, s)
  Forall "" t1 t2 -> do
    nm <- getNew
    (m,s) <- solve $ (nm, t1):context :|- t2
    return $ (Abstract nm t1 m, s)
  Forall nm t1 t2 -> do
    nm' <- getNew
    (v,s) <- solve $ (nm', t1):context :|- subst (nm |-> Cons nm') t2
    return $ (Cons "forall" .+. Abstract nm' t1 v, s)

solve :: Judgement -> Reification
solve judge@(context :|- r) = right judge <|> (msum $ useSingle (\f ctx -> left $ f:ctx :|- r) context)
  where useSingle f lst = sw id lst
          where sw _ [] = []
                sw placeOnEnd (a:lst) =  f a (placeOnEnd lst):sw (placeOnEnd . (a:)) lst

natural :: [(Name, Tp)] -> (Tm,Tp) -> Deduction
natural cont (tm,ty) = do
  let env = M.fromList cont
  io <- get    
  ((), i, constraints) <- lift $ runRWST (checkTerm env tm ty) () io
  s <- lift $ unifyEngine constraints i
  put $ variable s
  let sub = substitution s
  tell $ sub
  return $ sub 

sequent :: Environment -> Tp -> TypeChecker Tm
sequent env t = do
  i <- get 
  ((v,_),i',_) <- lift $ runRWST (solve $ M.toList env :|- t) () i
  put i'
  return v


----------------------------------------------------------------------
----------------------- LOGIC ENGINE ---------------------------------
----------------------------------------------------------------------
recSubst :: (Eq b, Subst b) => Substitution -> b -> b
recSubst s f = fst $ head $ dropWhile (not . uncurry (==)) $ iterate (\(_,b) -> (b,subst s b)) (f,subst s f)  

solver :: [(Name,Tp)] -> Tp -> Either String [(Name, Tm)]
solver axioms t = case runError $ runRWST (solve $ axioms :|- t) () 0 of
  Right ((tm,_),_,s) -> Right $ ("query" , varsToCons tm):(recSubst s $ map (\a -> (a,Var a)) $ S.toList $ freeVariables t)
    where varsToCons = subst $ M.fromList $ map (\(a,_) -> (a,Cons a)) axioms
  Left s -> Left $ "reification not possible: "++s
  
-----------------------------------------------------------------
----------------------- Type Checker ----------------------------    
-----------------------------------------------------------------
type Environment = M.Map Name Tp
type TypeChecker = RWST () [Constraint Tm] Integer Choice

class ToTm t where
  tpToTm :: t -> Tm
instance ToTm Tp where
  tpToTm (Forall n ty t) = Cons "forall" .+. Abstract n ty (tpToTm t)
  tpToTm (Atom tm) = tm
  tpToTm (t1 :->: t2) = Cons "->" .+. tpToTm t1 .+. tpToTm t2
instance (ToTm t) => ToTm (Maybe t) where
  tpToTm (Just t) = tpToTm t
  tpToTm Nothing = Hole

checkTerm :: Environment -> Tm -> Tp -> TypeChecker ()
checkTerm env v t = case v of
  Hole -> void $ sequent env t
  Cons nm -> case env ! nm of
    Nothing -> error $ nm++" was not found in the environment"
    Just t' -> 
      -- suppose t' has implicit arguments-  t' = c1 => t
      -- we then do a proof search for c1 and add it as an argument.
      tell [tpToTm t' :=: tpToTm t]
  Var nm -> case env ! nm of
    Nothing -> do 
      t'' <- sequent env t
      tell [t'' :=: v]
               -- in the mean time, assume there is only one use of each unbound variable
               -- error $ nm++" was not found in the environment"
    Just t' -> tell [tpToTm t' :=: tpToTm t]
  TyApp a b -> do
    nm <- getNew
    tv1 <- Atom <$> Var <$> getNew
    tv2 <- Var <$> getNew
    let t2 = tpToTm t
        tmB = tpToTm b
    checkTerm env a $ Forall nm tv1 (Atom tv2)
    checkTerm env tmB tv1  
    tell [tv2 :=: t2]
  App a b -> do
    v1 <- Atom <$> Var <$> getNew
    v2 <- Var <$> getNew
    tell [v2 :=: tpToTm t]
    checkTerm env a $ v1 :->: (Atom v2)
    checkTerm env b $ v1
  Abstract nm ty tm -> do
    v1 <- getNew
    v2 <- Atom <$> Var <$> getNew  -- why aren't we adding anything to the environment?
    checkTerm (M.insert v1 ty env) (subst (nm |-> Var v1) tm) v2
    tell [tpToTm t :=: tpToTm (Atom (Var v1) :->: v2 )]

getCons tm = case tm of
  Cons t -> return t
  App t1 t2 -> getCons t1
  TyApp t1 t2 -> getCons t1
  _ -> throwError $ "can't place a non constructor term here: "++ show tm

addVarsTm t = case t of
  App t1 t2 -> do
    t1' <- addVarsTm t1 
    t2' <- addVarsTm t2
    return $ App t1' t2'
  TyApp t1 t2 -> do
    t1' <- addVarsTm t1 
    t2' <- addVars t2
    return $ TyApp t1' t2'
  Abstract n t1 t2 -> do
    v <- addVars t1
    Abstract n v <$> addVarsTm t2
  Hole -> Var <$> getNew
  _ -> return t
  
addVars t = case t of
  Atom t -> Atom <$> addVarsTm t
  Forall n t1 t2 -> do
    v <- addVars t1
    Forall n v <$> addVars t2
  t1 :->: t2 -> do
    t1' <- addVars t1 
    t2' <- addVars t2
    return $ t1' :->: t2'

-- need to do a topological sort of types and predicates.
-- such that types get minimal correct bindings
checkType :: Environment -> Name -> Tp -> Choice Tp
checkType env base ty = do
  let checkTp env rms t = case t of
          Atom t -> do 
            when rms $ do
              c <- getCons t
              unless (null base || c == base) 
                $ throwError $ "non local name "++c++" expecting "++base
            checkTerm env t $ Atom $ Cons "atom"
          Forall n ty t -> do
            v1 <- getNew
            checkTp env False ty
            checkTp (M.insert v1 ty env) rms $ subst (n |-> Cons v1) t
          t1 :->: t2 -> do 
            checkTp env False t1
            checkTp env rms t2
  
  (tp',i,constraints) <- runRWST (do tp' <- addVars ty
                                     checkTp env True tp'
                                     return tp'
                                 ) () 0
  case runError $ unifyEngine constraints i of
    Left e  -> Fail $ "UNIFY FAILED: " ++ e
    Right s -> return $ subst (substitution s) tp'

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
  where atom = Atom $ Cons "atom"
        assumptions = M.fromList $ 
                      ("atom", atom): -- atom : atom is a given.
                      ("->", atom :->: atom :->: atom): -- atom : atom is a given.
                      ("forall", (atom :->: atom) :->: atom): -- atom : atom is a given.
                      ("exists", (atom :->: atom) :->: atom): -- atom : atom is a given.
                      concatMap (\st -> case st of
                                    Query _ _ -> []
                                    _ -> (predName st, predType st):predConstructors st) preds
