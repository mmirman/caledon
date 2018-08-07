{-# LANGUAGE ViewPatterns              #-}
module Src.AST where

import Names
import qualified Data.Map as M
import Control.DeepSeq
import Data.Monoid
import Src.Tracing
-------------
--- Terms ---
-------------
data Variable = DeBr Int 
              | Con Name 
              | Exi Int Name Type -- distance from the top, and type!
              deriving Eq

uncurriedExi ~(a,b,c) = Exi a b c

data P = P :+: N
       | Var Variable
       deriving Eq
                
data N = Abs Type N 
       | Pat P 
       deriving Eq

infixr 4 ++:
s ++: a = s++deepAppendError ("\nFROM: "++s) a

instance Show Variable where
  show (DeBr i) = show i
  show (Exi i n ty) = "("++n++"<"++show i++">:"++: show ty++")"
  show (Con n) = n

instance Show P where
  show (viewForallP -> Just (ty,p)) = "[ "++show ty++" ]  " ++: show p
  show (viewImpForallP -> Just (nm,ty,p)) = "{ "++nm++" : "++show ty ++" }  " ++: show p
  show (viewImpAbsP -> Just(nm,ty,a)) = "?λ"++nm++" : "++show ty ++: " . ("++ show a ++ ")"
  show (tipeView -> Init _) = "type'"
  show (a :+: b) = show a ++: " ( "++ show b++" ) "
  show (Var a) = show a
instance Show N where
  show (Abs ty a) = "λ:"++show ty ++: " . ("++ show a++")"

  show (Pat p) = show p


type Term = N
type Type = P

toTerm :: Type -> Term
toTerm p = Pat p

viewForallN (Pat p) = viewForallP p
viewForallN _ = Nothing

viewForallP (Var (Con "#forall#") :+: Pat ty :+: Abs ty' (Pat n) ) {- | ty == ty' -} = Just (ty,n)
--viewForallP (Var (Con "#forall#") :+: a :+: b@Abs{} ) = error $ "\nNot a forall type: [ "++show a ++ " ] "++show b
viewForallP _ = Nothing

viewForallPsimp (Var (Con "#forall#") :+: Pat ty :+: b ) = Just (ty,b)
viewForallPsimp _ = Nothing


viewImpForallN (Pat p) = viewImpForallP p
viewImpForallN _ = Nothing

viewImpForallP (Var (Con "#imp_forall#") :+: _ :+: (view_imp_name -> Just nm) :+: Abs ty (Pat n) ) = Just (nm,ty,n)
viewImpForallP cons@(Var (Con "#imp_forall#") :+: _ :+: _ :+: Abs{} ) = error $ "\nnot an imp_forall: "++show cons
viewImpForallP _ = Nothing

viewImpAbsN (Pat p) = viewImpAbsP p
viewImpAbsN _ = Nothing

viewImpAbsP (Var (Con "#imp_abs#") :+: _ :+: (view_imp_name -> Just nm) :+: Abs ty (Pat n) ) = Just (nm,ty,n)
viewImpAbsP cons@(Var (Con "#imp_abs#") :+: _ :+: _ :+: Abs{} ) = error $ "\nnot an imp_abs: "++show cons
viewImpAbsP _ = Nothing

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

fromType :: N -> P
fromType (Pat p) = p
fromType a = error $ "\nNot a type: "++show a

viewHead (p :+: _) = viewHead p
viewHead (Var v) = v

vvar = Var . DeBr
var = toTerm . vvar

evvar :: Int -> Name -> Type -> P
evvar i n t = Var $ Exi i n t

evar :: Int -> Name -> Type -> N
evar i n t = toTerm $ Var $ Exi i n t

vcon = Var . Con
con = toTerm . vcon

forall ty n = vcon "#forall#" :+: toTerm ty :+: Abs ty (toTerm n)

inameName = "#name#"
iname = vcon inameName
imp_name nm = toTerm $ iname :+: (toTerm nm) -- implement it like a string!

viewIname = (iname ==)

view_imp_name (Pat ((viewIname -> True) :+: (Pat (Var (Con nm))))) = Just nm
view_imp_name _ = Nothing


imp_abs nm ty n = vcon "#imp_abs#" :+: toTerm ty :+: imp_name (Var $ Con nm) :+: Abs ty (toTerm n)
imp_forall nm ty n = vcon "#imp_forall#" :+: toTerm ty :+: imp_name (Var $ Con nm) :+: Abs ty (toTerm n)

infixr 2 ~>
a ~> b = forall a b

tipeName = "type"
tipe = vcon tipeName



tipemake v = vcon "type" :+: (con $ "#%#"++v)

data TipeView = Init Name
              | Uninit
              | UniversalType
              | NotTipe
              deriving (Show, Eq, Read)
                         
tipeView (Var (Con "type") :+: (Pat (Var (Con ('#':'%':'#':v))))) = Init v
tipeView (Var (Con "type")) = Uninit
tipeView (Var (Con "type") :+: (Pat (Var (Con ("#universe#"))))) = UniversalType
tipeView _ = NotTipe

tipeViewN (Pat p) = tipeView p
tipeViewN _ = NotTipe
  
universeView (Var (Con ('#':'%':'#':v))) = Init v
universeView _ = NotTipe

isUniverse v = universeView v /= NotTipe

data Constant = Axiom Bool Int
              | Macro Term
              deriving (Show, Eq)

type Constants = M.Map Name (Constant,Type)

universeName = "#universe#"
universe = vcon universeName

tipeu = tipe :+: Pat universe

ulevelName = "#ulevel#"
ulevel = vcon ulevelName


constant a = (Axiom False $ -1000,a)
constants :: Constants
constants = M.fromList [ (tipeName, constant $ ulevel ~> tipeu )
                       , (universeName, constant $ ulevel)
                       , (ulevelName, constant $ ulevel )
                       , ("#forall#", constant $ forall tipeu $ (vvar 0 ~> tipeu) ~> tipeu)
                       , ("#ascribe#", constant $ forall tipeu $ vvar 0 ~> vvar 0)
                       --, ("#name#", constant tipeu)
                       --, ("#imp_forall#", constant $ forall tipeu $ (vvar 0 ~> tipeu) ~> tipeu)
                       --, ("#tycon#", constant $ iname ~> tipeu ~> tipeu)
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
                   

bind ty r = case r of
  Done -> Done
  _ -> Bind ty r                   
  
instance Monoid Form where
  mempty = Done
  mappend Done a = a
  mappend a Done = a
  mappend a b = a :&: b
  
  
instance Show Form where
  show (t1 :=: t2) = show t1 ++ " ≐ "++ show t2 
  show (t1 :<: t2) = show t1 ++ " < "++ show t2 
  show (t1 :<=: t2) =show t1 ++ " ≤ "++ show t2
  show (t1 :&: t2) = show t1 ++ " ∧ "++ show t2
  show (t1 :@: t2) = show t1 ++ " ∈  "++ show t2
  show (Bind t1 t2) = "∀: "++ show t1 ++: " .( "++show t2 ++ " )"
  show Done = " ⊤ "

instance NFData Form where
  rnf a = rnf $ show a
  
instance NFData N where
  rnf a = rnf $ show a
  
instance NFData P where
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
  addAt i (Pat p) = toTerm $ addAt i p

instance TERM Form where
  addAt v@(amount,thresh) (Bind ty n) = bind (addAt v ty) $ addAt (amount, thresh+1) n
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
                      
        
viewEquiv (a :=: b) = ((:=:), a, b)
viewEquiv (a :<: b) = ((:<:), a, b)
viewEquiv (a :<=: b) = ((:<=:), a, b)
viewEquiv _ = error "not an equivalence"
        
