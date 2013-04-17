{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE ViewPatterns              #-}
module Utwo where

import Control.Applicative 
import Control.Monad
import Data.Maybe
import Data.Functor
import qualified Data.Traversable as T
import qualified Data.Map as M

type Name = String

-------------------
--- Combinators ---
-------------------

onlyIf b = if b then Just () else Nothing

-- try a then b
a <+> b = do
  f <- a
  case f of
    Nothing -> b
    _ -> return $ Just f

a <?> b = case a of
  Nothing -> error b
  _ -> a

repeate 0 a = id
repeate 1 f = f
repeate n f = f . repeate (n-1) f


-------------
--- Terms ---
-------------
data Variable = DeBr Int | Con Name deriving (Eq, Show)

data P = P :+: N
       | Var Variable
       deriving (Eq, Show)
                
data N = Abs Type N 
       | Pat P 
       deriving (Eq, Show)
    
type Term = N
type Type = N

viewForall (Pat (Var (Con "#forall#") :+: _ :+: Abs ty n )) = (ty,n)

viewN (viewForall -> (ty,n)) = (ty:l,h)
  where (l,h) = viewN n
viewN (Pat p) = ([],p)

viewHead (p :+: n) = viewHead p
viewHead (Var v) = v

vvar = Var . DeBr
var = Pat . vvar

vcon = Var . Con
con = Pat . vcon

forall ty n = 
  Pat $ vcon "#forall#" :+: ty :+: Abs ty n

a ~> b = forall a b

tipeName = "type"
tipe = con tipeName

constants :: M.Map Name Type
constants = M.fromList [ (tipeName, tipe)
                       , ("#forall#", forall tipe $ (var 0 ~> tipe) ~> tipe)
                       ]

---------------
--- Formula ---
---------------
data Quant = Forall 
           | Exists
           deriving (Eq, Show)

data Form = Term :=: Term
          | Form :&: Form
          | Done
          | Bind Quant Type Form
          deriving (Eq, Show)

class Context a where
  getTy :: a -> Int -> Type

instance Context [Type] where
  getTy = (!!)
  
class TERM n where
  -- addAt (amount,thresh) r increases all variables referencing above the threshold down by amount
  addAt :: (Int,Int) -> n -> n
  -- liftAll i r  removes i abstractions off of r
  liftAll :: Int -> n -> n
  -- subst G (v,t) r is [v/ var 1 : t]_G r
  subst :: Context c => c -> (Term,Type) -> n -> n
  
instance TERM P where  
  addAt (amount,thresh) (Var (DeBr a)) = Var $ DeBr $ if a <= thresh then a else amount+a
  addAt _ (Var a) = Var a
  addAt i (p :+: n) = addAt i p :+: addAt i n
  
  liftAll i (Var (DeBr a)) = Var $ DeBr $ a + i
  liftAll i (Var a) = Var a
  
  liftAll i (p :+: n) = liftAll i p :+: liftAll i n
  
  subst = undefined
            
instance TERM N where  
  addAt v@(amount,thresh) (Abs ty n) = Abs (addAt v ty) $ addAt (amount, thresh+1) n
  addAt i (Pat p) = Pat $ addAt i p
  
  liftAll v (Abs ty n) = Abs (liftAll v ty) $ liftAll v n
  liftAll i (Pat p) = Pat $ liftAll i p
  
  subst = undefined

instance TERM Form where
  

app c n t = undefined



data Ctxt = Top 
          | L Ctxt Form 
          | R Form Ctxt 
          | B Ctxt Quant Type
           
start = Top 

upZero (L c f) = upZero c
upZero (R f c) = upZero c
upZero t = t

up (L c f) = up c
up (R f c) = up c
up (B c _ _) = upZero c
up t = t

upWithZero l Done = case l of
  L c f -> upWithZero c f
  R f c -> upWithZero c f
  _ -> (l, Done)
upWithZero (L c f) ctxt = upWithZero c $ ctxt :&: f
upWithZero (R f c) ctxt = upWithZero c $ f :&: ctxt
upWithZero t l = (t,l)

upWith l Done = case l of
  L c f -> upWith c f
  R f c -> upWith c f
  B c _ _ -> upWithZero c Done
  Top -> (Top, Done)
upWith (L c f) ctxt = upWith c $ ctxt :&: f
upWith (R f c) ctxt = upWith c $ f :&: ctxt
upWith (B c q ty) ctxt = upWithZero c $ Bind q ty ctxt
upWith Top ctxt = (Top, ctxt)


instance Context Ctxt where
  getTy c i = case repeate i up c of
    B _ _ ty -> ty

rebuild a Done = rebuildTop a
  where rebuildTop (B c q t) = rebuildTop c
        rebuildTop (L c t) = rebuild c t
        rebuildTop (R t c) = rebuild c t
        rebuildTop Top = Done
rebuild (B c q t) h = rebuild c $ Bind q t h
rebuild (L c t) h = rebuild c $ h :&: t
rebuild (R t c) h = rebuild c $ t :&: h
rebuild Top h = h


getPP :: P -> Maybe (Variable, [Int])
getPP p = case bpp p of
  Just (h,pp) -> Just (h, pp)
  Nothing -> Nothing
  where bpp (p :+: Pat (Var (DeBr v1))) = case bpp p of
          Just (h, pp) -> Just (h, v1:pp)
          Nothing -> Nothing
        bpp (Var h) = Just (h, [])
        bpp (p :+: _) = Nothing

viewPat p = (h, ml)
  where ~(h,ml) = vp p
        vp (p :+: m) = (h,m:ml)
          where ~(h,ml) = vp p
        vp (Var h) = (h,[])

gvarTy :: Ctxt -> Variable -> Maybe (Int,Type)
gvarTy ctxt (DeBr i) = case repeate i up ctxt of
  B _ Exists ty -> Just (i,ty)
  _ -> Nothing
gvarTy _ _ = Nothing  

uvarTy :: Ctxt -> Variable -> Maybe Type
uvarTy ctxt (Con c) = M.lookup c constants
uvarTy ctxt (DeBr i) = case repeate i up ctxt of
  B _ Forall ty -> Just ty
  _ -> Nothing  

-- | unify only performes transitions relating to "A :=: B". 
unify ctxt (a :&: b) = case unify (L ctxt b) a of
  Nothing -> unify (R a ctxt) b
  Just a  -> Just a
unify ctxt (Bind quant ty f) = unify (B ctxt quant ty) f
unify ctxt Done = Just $ rebuild ctxt Done
unify ctxt (a :=: b) = ueq (a,b) <|> ueq (b,a)
  where ueq (a,b) = case (a,b) of
          (Abs ty n1, n2) -> Just $ rebuild ctxt $ Bind Forall ty $ n1 :=: app ctxt (liftAll 1 n2) (var 0,ty)
          (Pat a, Pat b) -> identity a b <|> do
            (hA,ppA) <- getPP a
            (hA,tyA) <- gvarTy ctxt hA
            let a' = (hA,tyA,ppA)
            gvar_uvar a' b <|> gvar_gvar a' b  
          _ -> Nothing
        
        identity h1 h2 | h1 == h2 = Just $ rebuild ctxt Done

        gvar_uvar a b = do
          let (hB,mB) = viewPat b
          tyB <- uvarTy ctxt hB
          let b' = (hB, tyB, mB)
          gvar_uvar_outside a b' <|> gvar_uvar_inside a b'

        gvar_gvar a b = do
          (hB,ppB) <- getPP b
          (hB,tyB) <- gvarTy ctxt hB 
          let b' = (hB,tyB,ppB)
          gvar_gvar_same a b' <|> gvar_gvar_diff a b'
        
        gvar_uvar_inside  (hA,tyA,ppA) (hB,tyB,mB)  = undefined
        
        gvar_uvar_outside (hA,tyA,ppA) (hB,tyB,mB)  = undefined
        
        gvar_gvar_same    (hA,tyA,ppA) (hB,tyB,ppB) = do
          onlyIf $ hA == hB 
                && length ppA == length ppB
                && all (hA >) ppA
                && all (hA >) ppB

          
          let (ctxt,Bind Exists tyA' form) = repeate hA (uncurry upWith) (ctxt,Done)
           
          unless (tyA == tyB )  $ error "TYA!=TYB"
          unless (tyA == tyA' ) $ error "TYA!=TYA'"
          
              
          let (tyLst,tyBase) = viewN tyA
                            
              vty = foldr Abs (Pat tyBase) tyLst 
              
              sames = [ i | ((a,b),i) <- zip (zip ppA ppB) [0..], a == b ]
              
              mapping = M.fromList $ zip sames [0..]
              
              tyBase' = foldr app vty [ var $ fromMaybe 0 $ M.lookup i mapping | (_,i) <- zip ppA [0..] ]
              
              tyX' = foldr Abs tyBase tyLst
              l    = undefined
          return $ rebuild ctxt $ Bind Exists tyX' $ subst (B ctxt Exists tyX') (l, tyA) form
          
        
        gvar_gvar_diff    (hA,tyA,ppA) (hB,tyB,ppB) = undefined