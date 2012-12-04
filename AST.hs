{-# LANGUAGE  
 DeriveFunctor,
 FlexibleInstances
 #-}
module AST where

import qualified Data.Foldable as F
import Data.Monoid
import Data.Functor
import qualified Data.Map as M
import qualified Data.Set as S
--------------------------------------------------------------------
----------------------- DATA TYPES ---------------------------------
--------------------------------------------------------------------
type Name = String
              
data Variable = Var Name 
              | Cons Name 
              deriving (Ord, Eq)
                       
data Tm = Tipe Tp
        | Spine { binders     :: [(Name,Tp)]
                , constructor :: Variable
                , apps        :: [Tm] 
                }
        deriving (Eq)
                 
instance Ord Tm where                 
  Tipe t <= Tipe t' = t <= t'
  Tipe _ <= _ = True
  Spine absA consA appsA <= Spine absB consB appsB = 
    length absA <= length absB || appsA <= appsB || consA <= consB
                 
var nm = Spine [] (Var nm) []
cons nm = Spine [] (Cons nm) []

data Constraint a = a :=: a 
                  deriving (Eq, Ord, Functor, Show)

infixr 5 :->:
data Tp = Atom Tm
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
data Judgement = (:|-) { antecedent :: [(Name,Tp)] , succedent :: Tp }

--------------------------------------------------------------------
----------------------- PRETTY PRINT -------------------------------
--------------------------------------------------------------------
instance Show Variable where
  show (Var n) = n
  show (Cons n) = n

instance Show Tm where
  show (Tipe t) = show t
  show (Spine bindings cons apps) = "("++concatMap showQuant bindings
                                    ++show cons
                                    ++concatMap (\s -> " "++show s) apps
                                    ++")"
    where showQuant (nm,ty) = "\\"++nm++":"++show ty++"."
instance Show Tp where
  show (t :->: t') = "("++show t ++" -> "++ show t'++")"
  show (Atom t) = show t
  show (Forall nm t t') | not $ S.member nm (freeVariables t') = "("++show t ++" -> "++ show t'++") "
  show (Forall nm ty t) = "[ "++nm++" : "++show ty++" ] "++show t
  
instance Show Judgement where 
  show (a :|- b) =  removeHdTl (show a) ++" |- "++ show b
    where removeHdTl = reverse . tail . reverse . tail    

instance Show Predicate where
  show (Predicate nm ty []) =  ""++"defn "++nm++" : "++show ty++";"
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


rebuildSpine :: [(Name,Tp)] -> Tm -> [Tm] -> Tm
rebuildSpine binders = reb
  where reb (Tipe t) apps' = reb (tpToTm t) apps'
        reb (Spine [] c apps) apps' = Spine binders c (apps ++ apps')
        reb (Spine lst c apps) [] = Spine (binders++lst) c apps
        reb (Spine ((nm,_):l) c apps) (a:apps') = reb (subst (nm |-> a) $ Spine l c apps) apps'

class Subst a where
  subst :: Substitution -> a -> a
instance (Functor f , Subst a) => Subst (f a) where
  subst foo t = subst foo <$> t
  
instance Subst Tm where
  subst s (Tipe t) = Tipe $ subst s t
  subst s (Spine ((a,t):l) head apps) = Spine ((a,subst s t):l') head' apps'
    where Spine l' head' apps' = subst (M.delete a s) $ Spine l head apps
  subst s (Spine [] head apps) = let apps' = subst s <$> apps  in
    case head of
      Var nm | Just head' <- s ! nm -> rebuildSpine [] head' apps'
      _ -> Spine [] head apps'
instance Subst Tp where
  subst s t = case t of
    Atom t -> Atom $ subst s t
    Forall nm ty t -> Forall nm (subst s ty) $ subst (M.insert nm (var nm) s) t
    ty1 :->: ty2 -> subst s ty1 :->: subst s ty2
instance Subst Judgement where 
  subst foo (c :|- s) = subst foo c :|- subst foo s

--------------------------------------------------------------------
----------------------- FREE VARIABLES -----------------------------
--------------------------------------------------------------------
class FV a where         
  freeVariables :: a -> S.Set Name
  
instance FV a => FV (Maybe a) where
  freeVariables (Just f) = freeVariables f
  freeVariables Nothing = mempty
  
instance FV Tp where
  freeVariables t = case t of
    Forall a ty t -> (S.delete a $ freeVariables t) `S.union` (freeVariables ty)
    t1 :->: t2 -> freeVariables t1 `S.union` freeVariables t2
    Atom a -> freeVariables a
instance FV Tm where
  freeVariables t = case t of
    Tipe t -> freeVariables t
    Spine bound _ others -> F.foldr' (S.delete . fst) (mconcat $ freeVariables <$> others) bound 
instance (FV a,FV b) => FV (a,b) where 
  freeVariables (a,b) = freeVariables a `S.union` freeVariables b
  
  
  
class ToTm t where
  tpToTm :: t -> Tm
instance ToTm Tp where
  tpToTm (Forall n ty t) = Spine [] (Cons "forall") [rebuildSpine [(n,ty)] (tpToTm t) []]
  tpToTm (Atom tm) = tm
  tpToTm (t1 :->: t2) = Spine [] (Cons "->") [tpToTm t1 , tpToTm t2]
