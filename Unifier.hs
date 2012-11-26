{-# LANGUAGE 
 DeriveFunctor, 
 FlexibleContexts,  
 FlexibleInstances,
 ScopedTypeVariables 
 #-}
module Unifier where

import Choice
import Control.Monad (void)
import Control.Applicative ((<|>), empty)
import Control.Monad.Error (ErrorT, throwError, runErrorT, lift, unless, when)
import Control.Monad.State (StateT, get, put, runStateT, modify)
import Control.Monad.State.Class
import Control.Monad.RWS (RWST, RWS, get, put, tell, runRWST, runRWS, ask)
import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.Trans.Class
import Data.Maybe
import Data.Monoid
import Data.Functor
import Data.Foldable as F (msum, forM_)
import qualified Data.Map as M
import qualified Data.Set as S

--------------------------------------------------------------------
----------------------- DATA TYPES ---------------------------------
--------------------------------------------------------------------
type Name = String

infixl 6 .+.
(.+.) = App
              
data Tm = Var Name 
        | Cons Name
        | Abstract Name Tp Tm
        | App Tm Tm
        deriving (Eq, Ord)

data Constraint a = a :=: a 
                  deriving (Eq, Ord, Functor, Show)

infixr 5 :->:
data Tp = Atom Bool Tm
        | Exists Name Tp Tp
        | Forall Name Tp Tp
        | Tp :->: Tp
        deriving (Eq, Ord)

data Predicate = Predicate { predName::Name
                           , predType::Tp 
                           , predConstructors::[(Name, Tp)]
                           } 
               | Query { predName :: Name, predType::Tp }
               deriving (Eq)


infixl 1 :|- 
data Judgement = (:|-) { antecedent :: [Tp] , succedent :: Tp }

--------------------------------------------------------------------
----------------------- PRETTY PRINT -------------------------------
--------------------------------------------------------------------
instance Show Tm where
  show (App (App (Cons "->") a) b) = "("++show a++" -> "++show b++")"
  show (Abstract nm ty t) = "\\"++nm++":" ++show ty++"."++show t
  show (App a b) = "("++show a++" "++show b++")"
  show (Cons n) = n
  show (Var n) = "'"++n
  
instance Show Tp where
  show (t :->: t') = "("++show t ++" -> "++ show t'++")"
  show (Atom _ t) = show t
  show (Forall nm ty t) = "["++nm++" : "++show ty++"] "++show t
  show (Exists nm ty t) = "{"++nm++" : "++show ty++"} "++show t
  
instance Show Judgement where 
  show (a :|- b) =  removeHdTl (show a) ++" |- "++ show b
    where removeHdTl = reverse . tail . reverse . tail    


instance Show Predicate where
  show (Predicate nm ty (a:cons)) = 
      ""++"defn "++nm++" : "++show ty++"\n"
      ++  "  as "++showSingle a++concatMap (\x->
        "\n   | "++showSingle x) cons++";"
        where showSingle (nm,ty) = nm++" = "++show ty
  show (Query nm ty) = "query "++nm++" = "++show ty

--------------------------------------------------------------------
----------------------- SUBSTITUTION -------------------------------
--------------------------------------------------------------------
type Substitution = M.Map Name Tm  

infixr 0 |->
m1 *** m2 = M.union m2 (subst m2 <$> m1)
nil = M.empty
(|->) = M.singleton
(!) = flip M.lookup

class Subst a where
  subst :: Substitution -> a -> a
instance (Functor f , Subst a) => Subst (f a) where
  subst foo t = subst foo <$> t
instance Subst Tm where
  subst foo t = case t of
    Var nm -> fromMaybe t $! foo ! nm
    App t1 t2 -> App (subst foo t1) (subst foo t2)
    _ -> t
instance Subst Tp where
  subst s t = case t of
    Atom m t -> Atom m $ subst s t
    Forall nm ty t -> Forall nm (subst s ty) $ subst (M.insert nm (Var nm) s) t
    Exists nm ty t -> Exists nm (subst s ty) $ subst (M.insert nm (Var nm) s) t
    ty1 :->: ty2 -> subst s ty1 :->: subst s ty2
instance Subst Judgement where 
  subst foo (c :|- s) = subst foo c :|- subst foo s
                                      
--------------------------------------------------------------------
----------------------- UNIFICATION --------------------------------
--------------------------------------------------------------------
data St = St { substitution :: Substitution
             , constraints :: [Constraint Tm]
             , variable :: Integer 
             } 

type Unify a = StateT St Error a
    
nextConstraint :: ((Substitution, Constraint Tm) -> Unify ()) -> Unify ()
nextConstraint m = do
  st <- get
  case constraints st of
    [] -> return ()
    a:l -> do
      put $ st { constraints = l }
      m (substitution st,a)
      unify
      
putConstraints l = modify $ \s -> s { constraints = l++constraints s }

(+|->) :: Name -> Tm -> Unify ()
nm +|-> tm = modify $ \st -> st { substitution = M.insert nm tm $ subst (nm |-> tm) $ substitution st }
  
getNew :: Unify Name
getNew = do 
  st <- get 
  let n = 1 + variable st
  put $! st { variable = n }
  return $! show n

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
      putConstraints [ tipeToTerm ty :=: tipeToTerm ty' ]
      nm' <- getNew
      putConstraints [ subst (n |-> Cons nm') t :=: subst (n' |-> Cons nm') t' ] 
      unify      
    Cons nm :=: Cons nm' -> unless (nm == nm') badConstraint 
    App a b :=: App a' b' -> do
      putConstraints [a :=: a', b :=: b']
      unify
    _ :=: _ -> badConstraint

unifyEngine consts i = snd <$> runStateT unify (St nil consts i)
--------------------------------------------------------------------
----------------------- REIFICATION --------------------------------
--------------------------------------------------------------------
type Reifier = RWST () Substitution Integer Choice
type Reification = Reifier Substitution                                      

getNewVar :: MonadState Integer m => m String
getNewVar = do
  i <- get
  put (i+1)
  return $ show (i + 1)

unifier :: [Tp] -> Tp -> Reification 
unifier cons t = do
  t' <- case t of
    Atom _ k -> return k
    _ -> empty
  i <- get
  let isAtom (Atom _ _) = True
      isAtom _ = False
  F.msum $ flip map (filter isAtom cons) $ \(Atom _ con) -> 
    case runChoice $ unifyEngine [con :=: t'] i of
      Nothing -> empty
      Just s -> do
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
            nm' <- getNewVar
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
            nm' <- getNewVar
            solve $ (subst (nm |-> Cons nm') t2):context :|- r
          _ -> empty
          
rightFocused :: Judgement -> Reification
rightFocused judge@(context :|- r) = blurR judge soln
  where soln = case r of
          Atom True _ -> unifier context r
          Exists nm _ t1 -> do
            nm' <- getNewVar
            s <- rightFocused $ context :|- subst (nm |-> Var nm') t1
            return $ M.delete nm' s
          _ -> empty
          
rightUnfocused :: Judgement -> Reification
rightUnfocused judge@(context :|- r) = focusR judge soln
  where soln = case r of
          t1 :->: t2 -> solve $ t1:context :|- t2
          Forall nm _ t2 -> do
            nm' <- getNewVar
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
        fV (Var a) = S.singleton a
        fV (Cons _) = mempty

solver :: [Tp] -> Tp -> Either String [(Name, Tm)]
solver axioms t = case runChoice $ runRWST (solve $ axioms :|- t) () 0 of
  Nothing -> Left "reification not possible"
  Just (_,_,s) -> Right $ recSubst $ map (\a -> (a,Var a)) $ S.toList $ freeVariables t
    where recSubst f = fst $ head $ dropWhile (not . uncurry (==)) $ iterate (\(a,b) -> (b,subst s b)) (f,subst s f)


-----------------------------------------------------------------
----------------------- Type Checker ----------------------------    
-----------------------------------------------------------------
                       
type Environment = M.Map Name Tp
type TypeChecker = RWST Environment [Constraint Tm] Integer Error

tpToTm :: Tp -> TypeChecker Tm
tpToTm (Atom _ t) = return t
tpToTm (Forall n ty t) = do
  n' <- getNewVar
  tm <- tpToTm ty
  tell [ Var n' :=: tm]
  tr <- tpToTm $ subst (n |-> Var n') t
  return $ Cons "->" .+. Var n' .+. tr
tpToTm (Exists n ty t) = do
  n' <- getNewVar
  tm <- tpToTm ty
  tell [ Var n' :=: tm]
  tr <- tpToTm $ subst (n |-> Var n') t
  return $ Cons "->" .+. Var n' .+. tr
tpToTm (a :->: b) = do
  ta <- tpToTm a
  tb <- tpToTm b
  return $ Cons "->" .+. ta .+. tb

tipeToTerm (Forall n ty t) = Cons "forall" .+. Abstract n ty (tipeToTerm t)
tipeToTerm (Exists n ty t) = Cons "exists" .+. Abstract n ty (tipeToTerm t)
tipeToTerm (Atom _ tm) = tm
tipeToTerm (t1 :->: t2) = Cons "->" .+. tipeToTerm t1 .+. tipeToTerm t2

checkTerm :: Tm -> Tp -> TypeChecker ()
checkTerm (Cons nm) t' = do
  maybe_tenv <- (! nm) <$> ask
  case maybe_tenv of 
    Nothing -> error $ nm++" was not found in the environment"
    Just t -> do
      tm <- tpToTm t
      tm' <- tpToTm t'
      tell [tm :=: tm']
checkTerm v@(Var nm) t = do
  tm <- tpToTm t
  tell [ v :=: tm ] -- maybe? this might get weird. (nvm, necessary)
checkTerm (App a b) t = do
  v1 <- Atom True <$> Var <$> getNewVar
  v2 <- Var <$> getNewVar
  tm <- tpToTm t
  tell [v2 :=: tm]
  checkTerm a $ v1 :->: (Atom True v2)
  checkTerm b $ v1
checkTerm (Abstract nm ty tm) t = do
  v1 <- Var <$> getNewVar
  v2 <- Atom True <$> Var <$> getNewVar
  ty1 <- tpToTm ty
  tell [v1 :=: ty1]
  checkTerm (subst (nm |-> v1) tm) v2
  tym <- tpToTm t
  tym' <- tpToTm $ Atom True v1 :->: v2 
  tell [tym' :=: tym]

getCons tm = case tm of
  Cons t -> return t
  App t1 t2 -> getCons t1
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
            v1 <- Var <$> getNewVar
            checkTp False ty
            ty_tm <- tpToTm ty
            tell [ ty_tm :=: v1 ]
            checkTp rms $ subst (n |-> v1) t -- TODO
          Forall n ty t -> do
            v1 <- Var <$> getNewVar
            checkTp False ty
            ty_tm <- tpToTm ty
            tell [ ty_tm :=: v1 ]
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
        assumptions = M.fromList $ ("atom", atom): -- atom : atom is a given.
                                   ("->", atom :->: atom :->: atom): -- atom : atom is a given.
                                   ("forall", (atom :->: atom) :->: atom): -- atom : atom is a given.
                                   ("exists", (atom :->: atom) :->: atom): -- atom : atom is a given.
                      concatMap (\st -> case st of
                                    Query _ _ -> []
                                    _ -> (predName st, predType st):predConstructors st) preds
