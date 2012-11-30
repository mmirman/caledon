{-# LANGUAGE  
 DeriveFunctor,
 FlexibleInstances
 #-}
module AST where

import Data.Monoid
import Data.Maybe
import Data.Functor
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
        | TyApp Tm Tp
        deriving (Eq, Ord)

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
  
instance Show Tm where
  show (App (App (Cons "->") a) b) = "("++show a++" -> "++show b++")"
  show (App a b) = "("++show a++" "++show b++")"
  show (Abstract nm ty t) = "\\"++nm++":" ++show ty++"."++show t
--  show (TyApp a b) = "("++show a++" {"++show b++"} )"
  show (TyApp a b) = "("++show a++" "++show b++")"
  show (Cons n) = n
  show (Var n) = n
  
instance Show Tp where
  show (t :->: t') = "("++show t ++" -> "++ show t'++")"
  show (Atom t) = show t
  show (Forall "" t t') = "("++show t ++" -> "++ show t'++")"
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

class Subst a where
  subst :: Substitution -> a -> a
  
instance (Functor f , Subst a) => Subst (f a) where
  subst foo t = subst foo <$> t
instance Subst Tm where
  subst s t = case t of
    Var nm -> fromMaybe t $! s ! nm
    App t1 t2 -> App (subst s t1) (subst s t2)
    TyApp t1 t2 -> TyApp (subst s t1) (subst s t2)
    Abstract nm ty t -> Abstract nm (subst s ty) $ subst (M.insert nm (Var nm) s) t
    _ -> t
instance Subst Tp where
  subst s t = case t of
    Atom t -> Atom $ subst s t
    Forall nm ty t -> Forall nm (subst s ty) $ subst (M.insert nm (Var nm) s) t
    ty1 :->: ty2 -> subst s ty1 :->: subst s ty2
instance Subst Judgement where 
  subst foo (c :|- s) = subst foo c :|- subst foo s

--------------------------------------------------------------------
----------------------- FREE VARIABLES -----------------------------
--------------------------------------------------------------------
class FV a where         
  freeVariables :: a -> S.Set Name
instance FV Tp where                
  freeVariables (Forall a ty t) = (S.delete a $ freeVariables t) `S.union` (freeVariables ty)
  freeVariables (t1 :->: t2) = freeVariables t1 `S.union` freeVariables t2
  freeVariables (Atom a) = freeVariables a
instance FV Tm where
  freeVariables (App a b) = freeVariables a `S.union` freeVariables b
  freeVariables (TyApp a b) = freeVariables a `S.union` freeVariables b
  freeVariables (Abstract nm a b) = (S.delete nm $ freeVariables b) `S.union` freeVariables a
  freeVariables (Var a) = S.singleton a
  freeVariables (Cons _) = mempty
                           
instance (FV a,FV b) => FV (a,b) where 
  freeVariables (a,b) = freeVariables a `S.union` freeVariables b