{-# LANGUAGE DeriveFunctor, FlexibleContexts, ScopedTypeVariables #-}
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
        | Abstract Name Tm
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

infixl 1 :|- 
data Judgement = (:|-) { antecedent :: [Tp] , succedent :: Tp }

--------------------------------------------------------------------
----------------------- PRETTY PRINT -------------------------------
--------------------------------------------------------------------
instance Show Tm where
  show (App (App (Cons "->") a) b) = "("++show a++" -> "++show b++")"
  show (Abstract nm t) = "\\"++nm++"."++show t
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
    Abstract n t :=: Abstract n' t' -> do  
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
data Predicate = Predicate { predName::Name
                           , predType::Tp 
                           , predConstructors::[(Name, Tp)]
                           } 
               | Query { predType::Tp }
               deriving (Eq)
type Environment = M.Map Name Tp
type TypeChecker = RWST Environment [Constraint Tm] Integer Error

instance Show Predicate where
  show (Predicate nm ty (a:cons)) = 
      ""++"defn "++nm++" : "++show ty++"\n"
      ++  "  as "++showSingle a++concatMap (\x->
        "\n   | "++showSingle x) cons++";"
        where showSingle (nm,ty) = nm++" = "++show ty
  show (Query ty) = "query : "++show ty

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
  
  {- 
something like this possibly!
checkTerm (TyApp a b) t = do  
  v1 <- getNewVar
  v2 <- getNewVar
  checkTerm a $ Atom True $ Var v1
  checkTerm b $ Atom True $ Var v2
  tell [ tpToTm t :=: TyApp v1 (Cons v2) ]
  -}


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
typeCheckPredicate env (Query ty) = appendErr ("in query : "++ show ty) $ checkType env "" ty
typeCheckPredicate env pred = appendErr ("in\n"++show pred) $ do
  appendErr ("in name: "++ predName pred ++" = "++show (predType pred)) $
    checkType env "atom" (predType pred)
  forM_ (predConstructors pred) $ \(nm,ty) -> 
    appendErr ("in case: " ++nm ++ " = "++show ty) $ checkType env (predName pred) ty
  
typeCheckAll :: [Predicate] -> Error ()
typeCheckAll preds = forM_ preds $ typeCheckPredicate assumptions
  where assumptions = M.fromList $ ("atom", Atom True $ Cons "atom"): -- atom : atom is a given.
                      concatMap (\st -> case st of
                                    Query _ -> []
                                    _ -> (predName st, predType st):predConstructors st) preds

-----------------------------------------------------------------------
-------------------------- MAIN ---------------------------------------
-----------------------------------------------------------------------
main = do
  let var = Var
      cons = Cons
      
      tp = Atom False
      
      atom = tp $ Cons "atom"
      nat = tp $ Cons "nat"
      
      addRes a b c = tp $ cons "add" .+. a .+. b .+. c
      zero = cons "zero"
      succ a = cons "succ" .+. a
      
      infixr 5 $
      f $ i = f i
      infixr 4 =:
      (=:) a b = (a,b)
      infixl 3 |:
      (|:) foo a = foo a []
      infixl 2 <|
      foo <| a = foo { predConstructors = a:predConstructors foo }
      
      vr v = tp $ var v      
      lst v = tp $ cons "list" .+. var v

      predicates = [ Predicate "nat" |: atom
                     <| "zero" =: nat
                     <| "succ" =: nat :->: nat
                   , Predicate "add" |: nat :->: nat :->: nat :->: atom
                     <| "add-z" =: Forall "result" nat $ addRes zero (var "result") (var "result")
                     <| "add-s" =: Forall "m" nat $ Forall "n" nat $ Forall "res" nat $ addRes (var "n") (var "m") (var "res") :->: addRes (succ $ var "n") (var "m") (succ $ var "res")
                   , Predicate "list" |: atom :->: atom
                     <| "nil" =: Forall "a" atom $ lst "a"
                     <| "cons" =: Forall "a" atom $ vr "a" :->: lst "a" :->: lst "a"
                   , let cat v a b c = tp $ cons "concat" .+. var v .+. a .+. b .+. c
                         nil v = cons "nil" .+. var v
                         con v a b = cons "cons" .+. var v .+. a .+. b
                     in 
                     Predicate "concat" |: Forall "a" atom $ lst "a" :->: lst "a" :->: lst "a" :->: atom
                     <| "concat-nil" =: Forall "a" atom $ Forall "N" (lst "a") $ cat "a" (nil "a") (var "N") (var "N")
                     <| "concat-suc" =: Forall "a" atom $ Forall "V" (vr "a") $ Forall "N" (lst "a") $ Forall "M" (lst "a") $ Forall "R" (lst "a") $ 
                          cat "a" (var "N") (var "M") (var "R") 
                          :->: cat "a" (con "a" (var "V") (var "N")) (var "M") (con "a" (var "V") (var "R"))
                   ]
      
      target = Query $ addRes (succ $ succ $ zero) (var "what") (succ $ succ $ succ $ zero) 

  putStrLn $ "AXIOMS: "
  forM_ (target:predicates)  $ \s -> putStrLn $ show s++"\n"
      
  putStrLn "\nTYPE CHECKING: "
  case runError $ typeCheckAll $ target:predicates of
    Left e -> error e
    Right () -> putStrLn "Type checking success!"

  putStrLn $ "\nTARGET:\n\t"++show target

  case solver (snd <$> concatMap predConstructors predicates) (predType target) of
    Left e -> putStrLn $ "ERROR: "++e
    Right sub -> putStrLn $ "SOLVED WITH: "++(show $ sub)

{-
-------------------
  List A : atom


defn List : atom -> atom
  is nil  = [A] List A
   | succ = [A] A -> List A -> List A;

defn Nu : (atom -> atom) -> atom
  is Nu = [f : pred -> pred] f (Nu f) -> Nu f;
  
defn num : atom
  is zero = num
   | succ = num -> num;

defn accepts : (num -> atom) -> atom
  is Nu = [f : pred -> pred] f (Nu f) -> Nu f;

defn add : num -> num -> num -> atom
  is add-z = [N] N : nat -> add zero N N
   | add-s = [N][M][R] add N M R -> add (succ N) M $ succ R;

defn frikenKolio : num -> IO () -> atom
  is buildZero = frikenKolio N $ do putStrLn $ "hai" ++ show N;
                    
_$_ : [A][B] (A -> B) -> A -> B
f $ a = f a;

fooBar : IO ()
fooBar = do {
  let s = query[a] add (succ zero) (succ zero) a;
  putStrLn $ show s; 
}

 (OO)
  ##xxxxxxxxxxxxx------------------------
  ##xxxxxxxxxxxxx------------------------
  ##xxxxxxxxxxxxx------------------------
  ##xxxxxxxxxxxxx----AMERCA F**K YEAH ---
  ##xxxxxxxxxxxxx------------------------
  ##-------------------------------------
  ##-------------------------------------
  ##-------------------------------------
  ##-------------------------------------
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##  \o__
  ##   |
  ##  / \  .|.  /./ .  \.  .  \   
````````````````````````````````
:::::::;;;;;;;;;;;:;;;;;:;;:;;;;

-}

