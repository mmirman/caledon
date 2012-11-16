{-# LANGUAGE DeriveFunctor, FlexibleContexts, ScopedTypeVariables #-}
module Unifier where

import Choice
import Control.Applicative ((<|>), empty)
import Control.Monad.Error (ErrorT, throwError, runErrorT, lift, unless)
import Control.Monad.State (StateT, get, put, runStateT, modify)
import Control.Monad.State.Class
import Control.Monad.RWS (RWST, RWS, get, put, tell, runRWST, ask)
import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.Trans.Class
import Data.Maybe
import Data.Monoid
import Data.Functor
import Data.Foldable as F
import qualified Data.Map as M
import qualified Data.Set as S

--------------------------------------------------------------------
----------------------- DATA TYPES ---------------------------------
--------------------------------------------------------------------
type Name = String

infixl 1 .+.
(.+.) = App
              
data Tm = Var Name 
        | Cons Name
        | Abstract Name Tm
        | App Tm Tm
        deriving (Eq, Ord)

data Constraint a = a :=: a 
                  deriving (Eq, Ord, Functor, Show)

data Tp = Atom Bool Tm
        | Exists Name Tp
        | Forall Name Tp
        | (:->:) { ty1 :: Tp, ty2 :: Tp}
        | (:*:)  { ty1 :: Tp, ty2 :: Tp}
        | (:+:)  { ty1 :: Tp, ty2 :: Tp}
        deriving (Eq, Ord)

infixl 1 :|- 
data Judgement = (:|-) { antecedent :: [Tp] , succedent :: Tp }

--------------------------------------------------------------------
----------------------- PRETTY PRINT -------------------------------
--------------------------------------------------------------------
instance Show Tm where
  show (App a b) = "("++show a++" "++show b++")"
  show (Cons n) = "#"++n
  show (Var n) = ">"++n
  
instance Show Tp where
  show (t :+: t') = "("++show t ++" + "++ show t'++")"
  show (t :->: t') = "("++show t ++" -> "++ show t'++")"
  show (t :*: t') = "("++show t ++" * "++ show t'++")"
  show (Atom _ t) = show t
  show (Forall nm t) = "A|"++nm++". "++show t
  show (Exists nm t) = "E|"++nm++". "++show t
  
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
    Forall nm t -> Forall nm $ subst (M.insert nm (Var nm) s) t
    Exists nm t -> Exists nm $ subst (M.insert nm (Var nm) s) t
    _ -> t { ty1 = subst s $ ty1 t, ty2 = subst s $ ty2 t}
instance Subst Judgement where 
  subst foo (c :|- s) = subst foo c :|- subst foo s
                                      
--------------------------------------------------------------------
----------------------- UNIFICATION --------------------------------
--------------------------------------------------------------------
data St = St { substitution :: Substitution
             , constraints :: [Constraint Tm]
             , variable :: Integer 
             } 

type Unify a = StateT St (ErrorT String Identity) a
instance RunChoice (ErrorT String Identity) where 
  runChoice m = case runIdentity $ runErrorT m of
    Left e -> Nothing
    Right l -> Just l
    
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
unify = nextConstraint $ \(t, constraint@(a :=: b)) -> case (a :=: b) of
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
    Cons nm :=: Cons nm' -> unless (nm == nm') $ empty
    
    App a b :=: App a' b' -> do
      putConstraints [a :=: a', b :=: b']
      unify
    _ :=: _ -> empty

unifyEngine l i = runChoice $ snd <$> runStateT unify (St nil l i)

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
    case unifyEngine [con :=: t'] i of
      Nothing -> empty
      Just s -> do
        put $ variable s
        tell $ substitution s
        return $ substitution s

isPos t = case t of 
  _ :->: _ -> False
  Atom t _ -> t
  Forall _ _ -> False
  _ -> True 

blurL judge@(f:_ :|- _) soln  = if isPos f then solve judge else soln
focusL judge@(f:_ :|- _) soln = if isPos f then soln else leftFocused judge

blurR judge@(_ :|- r) soln = if isPos r then soln else solve judge
focusR judge@(_ :|- r) soln = if isPos r then rightFocused judge else soln

leftFocused :: Judgement -> Reification
leftFocused judge@(f:context :|- r) = blurL judge soln
  where soln = case f of
          Atom False _ -> unifier [f] r
          Forall nm t1 -> do
            nm' <- getNewVar
            s <- leftFocused $ subst (nm |-> Var nm') t1:f:context :|- r
            return $ M.delete nm' s
          t1 :->: t2 -> do
            s  <- rightFocused $ f:context :|- t1 -- could use GIpi but the BFS seems to be good enough.
            s' <- leftFocused $ subst s $ t2:context :|- r
            return $ s *** s'
          _ -> empty

leftUnfocused :: Judgement -> Reification
leftUnfocused judge@(f:context :|- r) = focusL judge soln
  where soln = case f of
          t1 :*: t2 -> solve $ t1:t2:context :|- r
          Exists nm t2 -> do
            nm' <- getNewVar
            solve $ (subst (nm |-> Cons nm') t2):context :|- r
          t1 :+: t2 -> solve (t1:context :|- r) <|> solve (t2:context :|- r)
          _ -> empty
          
rightFocused :: Judgement -> Reification
rightFocused judge@(context :|- r) = blurR judge soln
  where soln = case r of
          Atom True _ -> unifier context r
          Exists nm t1 -> do
            nm' <- getNewVar
            s <- rightFocused $ context :|- subst (nm |-> Var nm') t1
            return $ M.delete nm' s
          t1 :*: t2 -> do
            s <- rightFocused $ context :|- t1
            s' <- rightFocused $ subst s $ context :|- t2
            return $ s *** s'
          t1 :+: t2 -> rightFocused (context :|- t1) <|> rightFocused (context :|- t2)
          _ -> empty
          
rightUnfocused :: Judgement -> Reification
rightUnfocused judge@(context :|- r) = focusR judge soln
  where soln = case r of
          t1 :->: t2 -> solve $ t1:context :|- t2
          Forall nm t2 -> do
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

freeVariables (Forall a t) = S.delete a $ freeVariables t
freeVariables (Exists a t) = S.delete a $ freeVariables t
freeVariables (t1 :->: t2) = freeVariables t1 `S.union` freeVariables t2
freeVariables (t1 :*: t2) = freeVariables t1 `S.union` freeVariables t2
freeVariables (t1 :+: t2) = freeVariables t1 `S.union` freeVariables t2
freeVariables (Atom _ a) = fV a
  where fV (App a b) = fV a `S.union` fV b
        fV (Var a) = S.singleton a
        fV (Cons _) = mempty

solver :: [Tp] -> Tp -> Either String [(Name, Tm)]
solver axioms t = case runChoice $ runRWST (solve $ axioms :|- t) () 0 of
  Nothing -> Left "reification not possible"
  Just (_,_,s) -> Right $ recSubst $ map (\a -> (a,Var a)) $ S.toList $ freeVariables t
    where recSubst f = fst $ head $ dropWhile (not . uncurry (==)) $ iterate (\(a,b) -> (b,subst s b)) (f,subst s f)

-----------------------------------------------------------------------
-------------------------- MAIN ---------------------------------------
-----------------------------------------------------------------------
main = do
  let 
      var = Var
      cons = Cons
      
      addRes a b c = Atom False $ cons "add" .+. a .+. b .+. c
      zero = cons "zero"
      succ a = cons "succ" .+. a
      
      axioms = [ Forall "result" $ addRes zero (var "result") (var "result")
               , Forall "m" $ Forall "n" $ Forall "res" $ addRes (var "n") (var "m") (var "res") :->: addRes (succ $ var "n") (var "m") (succ $ var "res")
               ]
      target = addRes (succ $ succ $ zero) (var "what") (succ $ succ $ succ $ zero)
  putStrLn $ "AXIOMS: "
  forM_ axioms $ \s -> putStrLn $ "\t"++show s
  
  putStrLn $ "TARGET:\n\t"++show target
  case solver axioms target of
    Left e -> putStrLn $ "ERROR: "++e
    Right sub -> putStrLn $ "SOLVED WITH: "++(show $ sub)

-----------------------------------------------------------------
----------------------- Type Checker ----------------------------    
-----------------------------------------------------------------
    
type Environment = M.Map Name Tp
type TypeChecker = RWS Environment [Constraint Tm] Integer 

tpToTm :: Tp -> Tm
tpToTm (Atom _ t) = t
tpToTm (Forall n t) = Cons "|A" .+. Abstract n (tpToTm t)
tpToTm (Exists n t) = Cons "|E" .+. Abstract n (tpToTm t)
tpToTm (a :->: b) = Cons "->" .+. tpToTm a .+. tpToTm b
tpToTm (a :*: b) = Cons "*" .+. tpToTm a .+. tpToTm b
tpToTm (a :+: b) = Cons "+" .+. tpToTm a .+. tpToTm b

checkTerm :: Tm -> Tp -> TypeChecker ()
checkTerm (Cons nm) t = do
  tenv <- (M.! nm) <$> ask
  tell [tpToTm tenv :=: tpToTm t]
checkTerm v@(Var nm) t = do
  tell [ v :=: tpToTm t ] -- maybe? this might get weird. (nvm, necessary)
checkTerm (App a b) t = do
  v1 <- Atom True <$> Var <$> getNewVar
  v2 <- Atom True <$> Var <$> getNewVar
  tell [ tpToTm t :=: tpToTm v2]
  checkTerm a $ v1 :->: v2
  checkTerm b $ v1
  

data Predicate = Predicate { predName::Name
                           , predType::Tp 
                           , predConstructors::[(Name, Tp)]
                           } deriving (Show, Eq)

typeChecker :: [Predicate] -> Maybe ()
typeChecker preds   = undefined
  where assumptions = undefined

wellFormedPredicate :: Predicate -> Maybe ()
wellFormedPredicate pred = undefined

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

_$_ : [A][B] (A -> B) -> A -> B
f $ a = f a;

fooBar : IO ()
fooBar = do {
  let s = query[a] add (succ zero) (succ zero) a;
  putStrLn $ show s; 
}

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
  ##   /   \     //   \    \  .   
````````````````````````````````
:::::::;;;;;;;;;;;:;;;;;:;;:;;;;

-}

