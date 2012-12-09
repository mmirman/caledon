{-# LANGUAGE  
 DeriveFunctor,
 FlexibleInstances
 #-}
module AST where

import qualified Data.Foldable as F
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Functor
import qualified Data.Map as M
import qualified Data.Set as S
--------------------------------------------------------------------
----------------------- DATA TYPES ---------------------------------
--------------------------------------------------------------------
type Name = String
              
data Variable = Var  Name
              | Cons Name
              deriving (Ord, Eq)
                       
data Tm = AbsImp Name Tp Tm
        | Abs Name Tp Tm
        | Spine Variable [Tp] 
        deriving (Eq, Ord)
                 
var nm = Spine (Var nm) []
cons nm = Spine (Cons nm) []

data Constraint a = a :=: a
                  deriving (Eq, Ord, Functor, Show)

data Tp = Atom Tm
        | Forall Name Tp Tp
        | ForallImp Name Tp Tp
        deriving (Eq, Ord)

data Predicate = Predicate { predName::Name
                           , predType::Tp 
                           , predConstructors::[(Name, Tp)]
                           } 
               | Query { predName :: Name, predType::Tp }
               deriving (Eq)

infixl 1 :|-
data Judgement = (:|-) { antecedent :: [(Name,Tp)] , succedent :: Tp }


atom = Atom $ cons "atom"


--------------------------------------------------------------------
----------------------- PRETTY PRINT -------------------------------
--------------------------------------------------------------------
instance Show Variable where
  show (Var n)  = n
  show (Cons n) = n
showWithParens t = if (case t of
                          Forall _ _ _ -> True
                          Atom (Spine _ lst) -> not $ null lst
                          Atom (Abs _ _ _) -> True) then "("++show t++")" else show t 

instance Show Tm where
  show (Abs nm ty tm) = "λ "++nm++" : "++showWithParens ty++" . "++show tm
  show (AbsImp nm ty tm) = "?λ "++nm++" : "++showWithParens ty++" . "++show tm
  show (Spine cons apps) = show cons++concatMap (\s -> " "++showWithParens s) apps
instance Show Tp where
  show t = case t of
    Atom t -> show t
    Forall nm t t' | not (S.member nm (freeVariables t')) -> showWithParens++" → "++ show t'
      where showWithParens = case t of
              Forall _ _ _ -> "(" ++ show t ++ ")"
              _ ->  show t
    Forall nm ty t -> "∀ "++nm++" : "++show ty++" . "++show t
    
    ForallImp nm t t' | not (S.member nm (freeVariables t')) -> showWithParens++" ⇒ "++ show t'
      where showWithParens = case t of
              Forall _ _ _ -> "(" ++ show t ++ ")"
              _ ->  show t
    ForallImp nm ty t -> "?∀ "++nm++" : "++show ty++" . "++show t
  
instance Show Judgement where 
  show (a :|- b) =  removeHdTl (show a) ++" ⊢ "++ show b
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

infixr 1 |->
infixr 0 ***
m1 *** m2 = M.union m2 (subst m2 <$> m1)
(|->) = M.singleton
(!) = flip M.lookup


rebuildSpine :: Tm -> [Tp] -> Tm
rebuildSpine s [] = s
rebuildSpine (Spine c apps) apps' = Spine c (apps ++ apps')
rebuildSpine (Abs nm _ rst) (a:apps') = rebuildSpine (subst (nm |-> tpToTm a) $ rst) apps'

newName nm s = (nm',s')
  where s' = if nm == nm' then s else M.insert nm (var nm') s 
        nm' = fromJust $ find free $ nm:map (\s -> show s ++ "/") [0..]
        fv = mappend (M.keysSet s) (freeVariables s)
        free k = not $ S.member k fv

class Subst a where
  subst :: Substitution -> a -> a
instance (Functor f , Subst a) => Subst (f a) where
  subst foo t = subst foo <$> t
instance Subst Tm where
  subst s (Abs nm t rst) = Abs nm' (subst s t) $ subst s' rst
    where (nm',s') = newName nm s
  subst s (Spine head apps) = let apps' = subst s <$> apps  in
    case head of
      Var nm | Just head' <- s ! nm -> rebuildSpine head' apps'
      _ -> Spine head apps'
instance Subst Tp where
  subst s t = case t of
    Atom t -> Atom $ subst s t
    Forall nm ty t -> Forall nm' (subst s ty) $ subst s' t  -- THIS RULE is unsafe capture!
        where (nm',s') = newName nm s
instance Subst Judgement where 
  subst foo (c :|- s) = subst foo c :|- subst foo s

--------------------------------------------------------------------
----------------------- FREE VARIABLES -----------------------------
--------------------------------------------------------------------
class FV a where         
  freeVariables :: a -> S.Set Name
  
instance (FV a, F.Foldable f) => FV (f a) where
  freeVariables m = F.foldMap freeVariables m
instance FV Tp where
  freeVariables t = case t of
    Forall a ty t -> (S.delete a $ freeVariables t) `S.union` (freeVariables ty)
    Atom a -> freeVariables a
instance FV Tm where
  freeVariables t = case t of
    Abs nm t p -> S.delete nm $ freeVariables p
    Spine head others -> mappend (freeVariables head) $ mconcat $ freeVariables <$> others
instance FV Variable where    
  freeVariables (Var a) = S.singleton a
  freeVariables _ = mempty
instance (FV a,FV b) => FV (a,b) where 
  freeVariables (a,b) = freeVariables a `S.union` freeVariables b
  
class ToTm t where
  tpToTm :: t -> Tm
instance ToTm Tp where
  tpToTm (Forall n ty t) = Spine (Cons "forall") [Atom $ Abs n ty $ tpToTm t ]
  tpToTm (ForallImp n ty t) = Spine (Cons "forall") [Atom $ AbsImp n ty $ tpToTm t ]
  tpToTm (Atom tm) = tm
