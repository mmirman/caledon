{-# LANGUAGE  
 DeriveFunctor,
 FlexibleInstances,
 PatternGuards
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
              
data Variable = Var  {getName :: Name}
              | Cons {getName :: Name}
              deriving (Ord, Eq)
                       
data Argument = Impl { getTipe :: Tp } 
              | Norm  { getTipe :: Tp }
              deriving (Eq, Ord)

data Tm = AbsImp Name Tp Tm
        | Abs Name Tp Tm
        | Spine Variable [Argument] 
        deriving (Eq, Ord)

var nm = Spine (Var nm) []
cons nm = Spine (Cons nm) []
(~~>) a b = Forall "" a b 
(==>) a b = ForallImp "" a b 
infixr 1 :=:
data UnEq a = a :=: a
            deriving (Eq, Ord, Functor, Show)
                     
infixr 0 :@
data Constraint a = (UnEq a) :@ String
                  deriving (Eq, Ord, Functor)

instance Show a => Show (Constraint a) where                           
  show (u :@ f) = show u++"\n\tFROM: "++f
                           


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
data Judgement = (:|-) { antecedent :: [(Variable,Tp)] , succedent :: Tp }

atom = Atom $ cons "atom"

--------------------------------------------------------------------
----------------------- PRETTY PRINT -------------------------------
--------------------------------------------------------------------
instance Show Variable where
  show (Var n)  = '\'':n
  show (Cons n) = n
  
showWithParens t = if (case t of
                          Forall _ _ _ -> True
                          ForallImp _ _ _ -> True
                          Atom (Spine _ lst) -> not $ null lst
                          Atom (Abs _ _ _) -> True
                          Atom (AbsImp _ _ _) -> True
                      ) then "("++show t++")" else show t 

instance Show Argument where
  show (Impl t) = "{"++show t++"}"
  show (Norm t) = showWithParens t
instance Show Tm where
  show (Abs nm ty tm) = "λ "++nm++" : "++showWithParens ty++" . "++show tm
  show (AbsImp nm ty tm) = "?λ "++nm++" : "++showWithParens ty++" . "++show tm
  show (Spine cons apps) = show cons++concatMap (\s -> " "++show s) apps
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


rebuildSpine :: Tm -> [Argument] -> Tm
rebuildSpine s [] = s
rebuildSpine (Spine (Cons "forall") [Norm (Atom a)]) apps' = rebuildSpine a apps'
rebuildSpine (Spine c apps) apps' = Spine c (apps ++ apps')
rebuildSpine (Abs nm _ rst) (Norm a:apps') = rebuildSpine (subst (nm |-> toTm a) $ rst) apps'
rebuildSpine a@(Abs _ _ _) b@(Impl _:_) = error $ "attempting to apply an implied argument to a regular term: "++show a++" "++show b
rebuildSpine (AbsImp nm _ rst) (Impl a:apps') = rebuildSpine (subst (nm |-> toTm a) $ rst) apps'
rebuildSpine (AbsImp nm ty rst) apps' = AbsImp nm ty (rebuildSpine rst apps')

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
  subst s (AbsImp nm t rst) = AbsImp nm' (subst s t) $ subst s' rst
    where (nm',s') = newName nm s          
  subst s (Spine head apps) = let apps' = subst s <$> apps  in
    case head of
      Var nm | Just head' <- s ! nm -> rebuildSpine head' apps'
      _ -> Spine head apps'
instance Subst Argument where
  subst s a = a { getTipe = subst s $ getTipe a}
instance Subst Tp where
  subst s t = case t of
    Atom t -> Atom $ subst s t
    ForallImp nm ty t -> ForallImp nm' (subst s ty) $ subst s' t  -- THIS RULE is unsafe capture!
        where (nm',s') = newName nm s
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
instance FV Argument where  
  freeVariables = freeVariables . getTipe
instance FV Tp where
  freeVariables t = case t of
    Forall a ty t -> (S.delete a $ freeVariables t) `mappend` (freeVariables ty)
    ForallImp a ty t -> (S.delete a $ freeVariables t) `mappend` (freeVariables ty)
    Atom a -> freeVariables a
instance FV Tm where
  freeVariables t = case t of
    Abs nm t p -> (S.delete nm $ freeVariables p) `mappend` freeVariables t
    AbsImp nm t p -> (S.delete nm $ freeVariables p) `mappend` freeVariables t
    Spine head others -> mappend (freeVariables head) $ mconcat $ freeVariables <$> others
instance FV Variable where    
  freeVariables (Var a) = S.singleton a
  freeVariables _ = mempty
instance (FV a,FV b) => FV (a,b) where 
  freeVariables (a,b) = freeVariables a `S.union` freeVariables b
  
class ToTm t where  
  toTm :: t -> Tm

  
instance ToTm Argument where    
  toTm t = toTm $ getTipe t

instance ToTm Tp where  
  toTm (Forall n ty t) = Spine (Cons "forall") [Norm $ Atom $ Abs n ty $ toTm t ]
  toTm (ForallImp n ty t) = Spine (Cons "?forall") [Norm $ Atom $ AbsImp n ty $ toTm t]
  toTm (Atom tm) = tm

class ToTp t where
  toTp :: t -> Tp  

instance ToTp Tm where  
--  toTp (Spine (Cons "forall") [Norm (Atom (Abs nm ty t))]) = Forall nm (toTp ty) $ toTp t
--  toTp (Spine (Cons "forall") [Norm (Atom (AbsImp nm ty t))]) = ForallImp nm (toTp ty) $ toTp t
  
  toTp (Abs nm ty t) = Forall nm (toTp ty) $ toTp t  
  toTp (AbsImp nm ty t) = ForallImp nm (toTp ty) $ toTp t  
  toTp a = Atom $ toTpInt a
                     
toTpInt (Spine c l) = Spine c (map (\a -> a { getTipe = toTp $ getTipe a}) l)
toTpInt (Abs nm ty r) = Abs nm (toTp ty) (toTpInt r)
toTpInt (AbsImp nm ty r) = AbsImp nm (toTp ty) (toTpInt r)

instance ToTp Tp where
  toTp (Forall nm ty1 ty2) = Forall nm (toTp ty1) (toTp ty2)
  toTp (ForallImp nm ty1 ty2) = ForallImp nm (toTp ty1) (toTp ty2)
  toTp (Atom t) = toTp t  
  
  


class AllConsts a where         
  allConstants :: a -> S.Set Name
instance (AllConsts a, F.Foldable f) => AllConsts (f a) where
  allConstants m = F.foldMap allConstants m
instance AllConsts Argument where  
  allConstants = allConstants . getTipe
instance AllConsts Tp where
  allConstants t = case t of
    Forall a ty t -> (allConstants t) `mappend` (allConstants ty)
    ForallImp a ty t -> (allConstants t) `mappend` (allConstants ty)
    Atom a -> allConstants a
instance AllConsts Tm where
  allConstants t = case t of
    Abs nm t p -> allConstants p `mappend` allConstants t
    AbsImp nm t p -> allConstants p  `mappend` allConstants t
    Spine head others -> mappend (allConstants head) $ mconcat $ allConstants <$> others
instance AllConsts Variable where    
  allConstants (Cons a) = S.singleton a
  allConstants _ = mempty
instance (AllConsts a,AllConsts b) => AllConsts (a,b) where 
  allConstants (a,b) = allConstants a `S.union` allConstants b