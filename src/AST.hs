{-# LANGUAGE ViewPatterns              #-}
module Src.AST where

import Names
import qualified Data.Map as M
import Control.DeepSeq
import Data.Monoid
-------------
--- Terms ---
-------------
data Variable = DeBr Int 
              | Con Name 
              | Exi Int Name Type -- distance from the top, and type!
              deriving (Eq,Ord)

uncurriedExi ~(a,b,c) = Exi a b c

data P = P :+: N
       | Var Variable
       deriving (Eq, Ord)
                
data N = Abs Type N 
       | ImpAbs Name Type N
       | Pat P 
       deriving (Eq, Ord)
    
instance Show Variable where
  show (DeBr i) = show i
  show (Exi i n ty) = n++"<"++show i++">"
  show (Con n) = n

instance Show P where
  show (viewForallP -> Just (ty,p)) = "[ "++show ty ++" ]  "++ show p
  show (viewImpForallP -> Just (nm,ty,p)) = "{ "++nm++" : "++show ty ++" }  "++ show p
  show (a :+: b) = show a ++" ( "++ show b++" ) "
  show (Var a) = show a
instance Show N where
  show (Abs ty a) = "λ:"++show ty ++" . ("++ show a++")"
  show (ImpAbs nm ty a) = "?λ"++nm++" : "++show ty ++" . ("++ show a++")"
  show (Pat p) = show p


type Term = N
type Type = P

viewForallN (Pat p) = viewForallP p
viewForallN _ = Nothing

viewForallP (Var (Con "#forall#") :+: _ :+: Abs ty (Pat n) ) = Just (ty,n)
viewForallP cons@(Var (Con "#forall#") :+: _ :+: Abs{} ) = error $ "not a type: "++show cons
viewForallP _ = Nothing

viewImpForallN (Pat p) = viewImpForallP p
viewImpForallN _ = Nothing

viewImpForallP (Var (Con "#imp_forall#") :+: _ :+: ImpAbs nm ty (Pat n) ) = Just (nm,ty,n)
viewImpForallP cons@(Var (Con "#imp_forall#") :+: _ :+: ImpAbs{} ) = error $ "not a type: "++show cons
viewImpForallP _ = Nothing

data Fam = Poly 
         | Family Variable 
         deriving (Eq, Show)

getFamily :: P -> Fam
getFamily = getFamily' 0
  where getFamily' i (viewForallP -> Just (_,n)) = getFamily' (i + 1) n
        getFamily' i p = case viewHead p of
          DeBr j -> if j < i 
                    then Poly 
                    else Family $ DeBr $ j - i
          c -> Family c

viewP (viewForallP -> Just ~(ty,n)) = (ty:l,h)
  where ~(l,h) = viewP n
viewP p = ([],p)

fromType (Pat p) = p
fromType a = error $ "not a type: "++show a

viewHead (p :+: _) = viewHead p
viewHead (Var v) = v

vvar = Var . DeBr
var = Pat . vvar

evvar :: Int -> Name -> Type -> P
evvar i n t = Var $ Exi i n t

evar :: Int -> Name -> Type -> N
evar i n t = Pat $ Var $ Exi i n t

vcon = Var . Con
con = Pat . vcon

forall ty n = vcon "#forall#" :+: Pat ty :+: Abs ty (Pat n)

imp_forall nm ty n = vcon "#imp_forall#" :+: Pat ty :+: ImpAbs nm ty (Pat n)

a ~> b = forall a b

tipeName = "type"
tipe = vcon tipeName

tipemake v = vcon "type" :+: (con $ '#':v)

data TipeView = Init Name
              | Uninit
              | NotTipe

tipeView (Var (Con "type") :+: (Pat (Var (Con ('#':v))))) = Init v
tipeView (Var (Con "type")) = Uninit
tipeview _ = NotTipe
  

data Constant = Axiom Bool Int
              | Macro Term
              deriving (Show, Eq)

type Constants = M.Map Name (Constant,Type)

constant a = (Axiom False $ -1000,a)

constants :: Constants
constants = M.fromList [ (tipeName, constant tipe)
                       , ("#forall#", constant $ forall tipe $ (vvar 0 ~> tipe) ~> tipe)
                       ]
            
---------------
--- Formula ---
---------------
infixr 2 :&:
infix 3 :=:

data Form = Term :=: Term
          | Term :<=: Term
          | Term :<: Term
            
          | Term :@: Type
          | Form :&: Form
          | Done
          | Bind Type Form
          deriving Eq
                   
                   
instance Monoid Form where
  mempty = Done
  mappend Done a = a
  mappend a Done = a
  mappend a b = a :&: b
  
  
instance Show Form where
  show (t1 :=: t2) = show t1 ++ " ≐ "++ show t2
  show (t1 :<: t2) = show t1 ++ " < "++ show t2
  show (t1 :<=: t2) = show t1 ++ " ≤ "++ show t2
  show (t1 :&: t2) = " ( "++show t1 ++ " ) ∧ ( "++ show t2++" )"
  show (t1 :@: t2) = " ( "++show t1 ++ " ) ∈ ( "++ show t2++" )"
  show (Bind t1 t2) = " ∀: "++ show t1 ++ " . "++show t2
  show Done = " ⊤ "

instance NFData Form where
  rnf a = rnf $ show a



class TERM n where
  -- addAt (amount,thresh) r increases all variables referencing above the threshold down by amount
  addAt :: (Int,Int) -> n -> n
  
instance TERM Variable where  
  addAt (amount,thresh) (DeBr a) = DeBr $ if   a <= thresh 
                                          then a 
                                          else amount + a
  addAt i (Exi j nm ty) = Exi j nm $ addAt i ty
  addAt _ a = a
  
instance TERM P where  
  addAt i (Var a) = Var $ addAt i a
  addAt i (p :+: n) = addAt i p :+: addAt i n
instance TERM N where  
  addAt v@(amount,thresh) (Abs ty n) = Abs (addAt v ty) $ addAt (amount, thresh+1) n
  addAt i (Pat p) = Pat $ addAt i p

instance TERM Form where
  addAt v@(amount,thresh) (Bind ty n) = Bind (addAt v ty) $ addAt (amount, thresh+1) n
  addAt i (p :=: n) = addAt i p :=: addAt i n
  addAt i (p :<: n) = addAt i p :<: addAt i n
  addAt i (p :<=: n) = addAt i p :<=: addAt i n
  addAt i (p :&: n) = addAt i p :&: addAt i n
  addAt i (p :@: n) = addAt i p :@: addAt i n
  addAt _ Done = Done
  
liftV :: TERM n => Int -> n -> n
liftV v = addAt (v,-1) 

type Reconstruction = M.Map Name ( Int {- depth -} 
                                 , Term {- reconstruction -}
                                 ) 