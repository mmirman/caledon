{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ScopedTypeVariables       #-}
module Utwo where

import Control.Applicative 
import Control.Monad
import Data.Monoid
import Data.Maybe
import Data.Functor
import qualified Data.Traversable as T
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace

vtrace l a = trace (l++": "++show a)

type Name = String
-- This unification algorithm isn't the best for existential name recovery!
-- in fact, how can we even do it?
-- Exists (Maybe Name)?
-- associate a debruin existential with a perminant 
-- named existential? and perform a contextual substitution?

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

repeate 0 f = id
repeate n f = f . repeate (n-1) f


-------------
--- Terms ---
-------------
data Variable = DeBr Int | Con Name deriving Eq

data P = P :+: N
       | Var Variable
       deriving (Eq)
                
data N = Abs Type N 
       | Pat P 
       deriving (Eq)
    

instance Show Variable where
  show (DeBr i) = show i
  show (Con n) = n

instance Show P where
  show (viewForallP -> Just (ty,p)) = "( "++show ty ++" ) ~> ( "++ show p++" )"
  show (a :+: b) = show a ++" ( "++ show b++" ) "
  show (Var a) = show a
instance Show N where
  show (Abs ty a) = "λ:"++show ty ++" . ("++ show a++")"
  show (Pat p) = show p

type Term = N
type Type = N

viewForallP (Var (Con "#forall#") :+: _ :+: Abs ty n ) = Just (ty,n)
viewForallP _ = Nothing

viewForallN (Pat p) = viewForallP p
viewForallN _ = Nothing

viewN (viewForallN -> Just (ty,n)) = (ty:l,h)
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

infixr 1 ~>
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

infix 2 :&:
infix 3 :=:

data Form = Term :=: Term
          | Form :&: Form
          | Done
          | Bind Quant Type Form
          deriving Eq

instance Show Form where
  show (t1 :=: t2) = show t1 ++ " ≐ "++ show t2
  show (t1 :&: t2) = " ( "++show t1 ++ " ) ∧ ( "++ show t2++" )"
  show (Bind Forall t1 t2) = " ∀: "++ show t1 ++ " . "++show t2
  show (Bind Exists t1 t2) = " ∃:"++ show t1 ++ " . "++show t2
  show Done = " ⊤ "
  

class Show a => Context a where
  getTy :: a -> Variable -> Type
  putTy :: a -> Type -> a
instance Context [Type] where
  getTy v (DeBr a) = liftV (-a) $ v !! a
  getTy v (Con a) = constants M.! a
  
  putTy c t = t:c
  
class TERM n where
  addAt :: (Int,Int) -> n -> n

  
instance TERM P where  
  addAt (amount,thresh) (Var (DeBr a)) = Var $ DeBr $ if a < thresh then a else amount+a
  addAt _ (Var a) = Var a
  addAt i (p :+: n) = addAt i p :+: addAt i n
            
instance TERM N where  
  addAt v@(amount,thresh) (Abs ty n) = Abs (addAt v ty) $ addAt (amount, thresh+1) n
  addAt i (Pat p) = Pat $ addAt i p
  
instance TERM Form where
  addAt v@(amount,thresh) (Bind q ty n) = Bind q (addAt v ty) $ addAt (amount, thresh+1) n
  addAt i (p :=: n) = addAt i p :=: addAt i n
  addAt i (p :&: n) = addAt i p :&: addAt i n
  addAt i Done = Done
    
liftV :: TERM n => Int -> n -> n
liftV v = addAt (v,0) 

liftThree i (a,b,c) = (liftV i a, liftV i b, i + c)

etaExpand :: Type -> P -> N
etaExpand (viewForallN -> Just (a,b)) m = Abs a $ Pat $ liftV 1 m :+: etaExpand (liftV 1 a) (vvar 0)
etaExpand _ m = Pat m

substN :: Context c => Bool -> c -> (Term,Type, Int) -> N -> N
substN t ctxt na (Pat p) = case substP t ctxt na p of
  (Right m,p) -> m
  (Left m, p) -> if t then etaExpand p m else Pat m
substN t ctxt na (Abs b n) = Abs (substN t ctxt na b) $ substN t (putTy ctxt b) (liftThree 1 na) n

substP :: Context c => Bool -> c -> (Term,Type,Int) -> P -> (Either P N, Type)
substP t ctxt (n,ty,x') (Var (DeBr x)) | x == x' = (Right n, ty)
substP t ctxt na (y@(Var v)) = (Left y, getTy ctxt v)
substP t ctxt na (p :+: n) = hered t ctxt (substP t ctxt na p) (substN t ctxt na n)

hered  :: Context c => Bool -> c -> (Either P N, Type) -> N -> (Either P N, Type)
hered t ctxt (Right (Abs a1 n), ~(viewForallN -> ~(Just ~(a1',a2)))) nv = 
  ( Right $ substN t ctxt (nv,a1,-1) $ addAt (-1,0) n
  , substN False ctxt (nv, a1',-1) $ addAt (-1,0) a2
  )
hered t ctxt (Right (Pat p1), ~(viewForallN -> ~(Just ~(a1',a2)))) nv = 
  ( Right $ Pat $ p1 :+: nv
  , substN False ctxt (nv, a1',-1) $ addAt (-1,0) a2
  )
hered t ctxt (Left p1, ~(viewForallN -> ~(Just ~(a1',a2)))) nv = 
  ( Left $ p1 :+: nv
  , substN False ctxt (nv, a1',-1) $ addAt (-1,0) a2
  )

      
substF :: Context c => c -> (Term,Type,Int) -> Form -> Form  
substF _ _ Done = Done
substF ctxt sub (a :=: b) = substN True ctxt sub a :=: substN True ctxt sub b
substF ctxt sub (a :&: b) = substF ctxt sub a :&: substF ctxt sub b
substF ctxt sub (Bind q ty f) = 
  Bind q (substN True ctxt sub ty) $ substF (putTy ctxt ty) (liftThree 1 sub) f

app  :: Context c => c -> Either P N -> N -> Either P N
app ctxt (Right (Abs a1 n)) nv = Right $ substN True ctxt (nv,a1,-1) $ addAt (-1,0) n
app ctxt (Right (Pat p1)) nv = Right $ Pat (p1 :+: nv)
app ctxt (Left p1) nv = Left $ p1 :+: nv

appN c p n = case app c (Right p) n of
  Right n -> n
  Left p -> Pat p


data Ctxt = Top 
          | L Ctxt Form 
          | R Form Ctxt 
          | B Ctxt Quant Type deriving (Eq, Show)
           
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

upDone i (a,b) = upDone' i (upWithZero a b)
  where upDone' (-1) (ctxt,Done) = Nothing
        upDone' (-1) (ctxt,nxt)  = Just (ctxt,nxt)
        upDone' i (ctxt,nxt) = upDone' (i-1) (upWith ctxt nxt)

instance Context Ctxt where
  getTy c (Con i) = constants M.! i
  getTy c (DeBr i) = case repeate i up $ upZero c of
    B _ _ ty -> ty
    Top -> error $ "\nI: "++show i++"\nCTXT: "++show c
  putTy c ty = B c Forall ty
  
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
gvarTy ctxt (DeBr i) = case repeate i up $ upZero ctxt of
  B _ Exists ty -> Just (i,ty)
  _ -> Nothing
gvarTy _ _ = Nothing  

uvarTy :: Ctxt -> Variable -> Maybe Type
uvarTy ctxt (Con c) = M.lookup c constants
uvarTy ctxt (DeBr i) = case repeate i up $ upZero ctxt of
  B _ Forall ty -> Just ty
  _ -> Nothing  

isForall ctxt c = case uvarTy ctxt (DeBr c) of
  Just a  -> True
  Nothing -> False

inj = inj mempty
  where inj m [] = True
        inj m (a:l) = not (S.member a m) && inj (S.insert a m) l



-- | unify only performes transitions relating to "A :=: B". 
unify ctxt (a :&: b) = case  unify (L ctxt b) a of
  Nothing -> unify (R a ctxt) b
  Just a  -> Just a
unify ctxt (Bind quant ty f) = unify (B ctxt quant ty) f
unify ctxt Done = Just $ rebuild ctxt Done
unify ctxt (a :=: b) = ueq (a,b) <|> ueq (b,a)
  where ueq (a,b) = case (a,b) of
          (Abs ty n1, n2) -> Just $ rebuild ctxt $ Bind Forall ty $ n1 :=: appN ctxt (liftV 1 n2) (var 0)
          (Pat a, Pat b) -> identity a b <|> do
            (hA,ppA) <- getPP a
            (hA,tyA) <- gvarTy ctxt hA
            let a' = (hA,tyA,ppA)
            onlyIf $ partialPerm hA ppA                
            gvar_uvar a' b <|> gvar_gvar a' b  
          _ -> Nothing
          
        partialPerm hA ppA = all (hA >) ppA && all (isForall ctxt) ppA && inj ppA
        
        identity h1 h2 | h1 == h2 = Just $ rebuild ctxt Done
        identity h1 h2 = Nothing

        gvar_uvar a b = do
          let (hB,mB) = viewPat b
          tyB <- uvarTy ctxt hB
          let b' = (hB, tyB, mB)
          gvar_uvar_outside a b' <|> gvar_uvar_inside a b'

        gvar_gvar a b = do
          (hB,ppB) <- getPP b
          (hB,tyB) <- gvarTy ctxt hB
          let b' = (hB,tyB,ppB)
          onlyIf $ partialPerm hB ppB
          gvar_gvar_same a b' <|> gvar_gvar_diff a b'
        
        
        gvar_gvar_same (hA,tyA,ppA) (hB,tyB,ppB) = do
          onlyIf $ hA == hB 
                && length ppA == length ppB
          let (tyLst,tyBase) = viewN tyA
                  
              -- could be made way more efficient
              tyX' = getTyLst tyLst (zip ppA ppB)
                where getTyLst [] [] = Pat $ tyBase
                      getTyLst (ty:c) ((a,b):lst) | a == b = forall ty $ getTyLst c lst
                      getTyLst (ty:c) (_:lst) = liftV (-1) $ getTyLst c lst
              (tyLst',tyBase') = viewN tyX'
              
              base = foldl (:+:) (vvar $ length tyLst) [ var i | ((a,b),i) <- zip (zip ppA ppB) [0..], a == b ]
              l  = foldr Abs (Pat base) tyLst
          -- could make this even more efficient by only performing the 
          -- "upDone step once along side the search for tyA', but why bother?"    
          case upDone hA (ctxt,Done) of 
            -- in this case, we don't actually care about the result since it isn't in an exists.            
            Nothing -> return $ rebuild ctxt Done
            Just (ctxt,Bind Exists tyA' form) -> do
              unless (tyA == tyB  ) $ error "gvar_gvar_same: TYA!=TYB"
              unless (tyA == tyA' ) $ error "gvar_gvar_same: TYA!=TYA' - implying repeate off"

              return $ rebuild ctxt $ Bind Exists tyX' $ substF (putTy ctxt tyX') (l, tyA,0) form
        
        gvar_uvar_outside (hA,tyA,ppA) (hB,tyB,mB) = do
          onlyIf $ case hB of
            Con _ -> True
            DeBr hBj -> hA < hBj 
          
          let (tyLstA,tyBaseA) = viewN tyA
              (tyLstB,tyBaseB) = viewN tyB
              
              lun = length tyLstA
              n = lun - 1                          
              
              un_lst = var <$> [0..n]
              
              xs = ((lun +) . fst) <$> zip [0..] tyLstB
              xMlst = map (\x -> Pat $ foldl (:+:) (vvar x) un_lst) xs
              base = Pat $ foldl (:+:) (Var hB) $ xMlst

              l = foldr Abs base $ zipWith liftV [0..] tyLstA
                      
          -- could make this even more efficient by only performing the 
          -- "upDone step once, but why bother?"
          case upDone hA (ctxt,Done) of 
            Nothing -> return $ rebuild ctxt Done
              -- in this case, we don't actually care about the result since it isn't in an exists.
            Just (ctxt,Bind Exists tyA' form) -> do
              
              unless (tyA == tyA' ) $ error "gvar_uvar_outside: TYA!=TYA' - implying repeate off"
              let foralls i v = foldr forall v $ forallsA i
                          
                  forallsA i = fst $ viewN $ liftV i $ foldr forall tipe tyLstA

                  build []         i b'lst _      _   _    = reverse $ b'lst
                  build (b_i:blst) i b'lst ctxt_p f_p l_p  = build blst (i+1) (b'_i:b'lst) ctxt_i f_i l_i
                    where b'_p = head b'lst
                          f_i c b = appN c (f_p c b) $! Pat $! foldl (:+:) (vvar $ n + i - 1 ) un_lst
                          l_i = Abs b_i . l_p
                                  
                          ctxt_i = putTy ctxt_p b'_p
                          ctxt_iU = foldr (flip putTy) ctxt_i (forallsA i)
                          b'_i = foralls i $ f_i ctxt_iU $ l_i $ addAt (n+i,i) b_i
                          
                  -- sooo tricky to implement with debruijn!
                  bNlst = build tyLstB 0 [] ctxt (\ctxt -> id) id                
                  
              return $ rebuild ctxt 
                $ foldr (\xN -> Bind Exists xN) 
                        (substF (foldr (flip putTy) ctxt bNlst) (l, tyA , 0) $ addAt (length bNlst - 1, 1) form)
                $ bNlst
              
        gvar_uvar_inside  (hA,tyA,ppA) (hB,tyB,mB)  = Nothing
        
        gvar_gvar_diff    (hA,tyA,ppA) (hB,tyB,ppB) = Nothing

{-
  F_0 = id
  L_0 = id

  B'_{i-1}
  F_{i-1}

  ctxt_i = ctxt_{i-1},B'_{i-1}
  F_i ctxt b = H(ctxt, F_{i-1} ctxt b, (i+n - 1) (n - 1) ... 0)
  L_i b = \B_i.L_{i-1} b
  B'_i  = (A_1...A_n)^i . F_i (ctxt_i,(A_1...A_n)^i) (L_i (B_i^{n+i,i}))
-}
test3 :: Form
test3 = Bind Exists ((tipe ~> tipe) ~> tipe ~> (tipe ~> tipe) ~> tipe) -- 3
      $ Bind Forall (tipe ~> tipe)-- 2
      $ Bind Forall (tipe ~> tipe) -- 1 
      $ Bind Forall tipe -- 0 
--      $ Pat (vvar 3 :+: (Abs tipe $ Pat $ vvar 2 :+: var 0) :+: var 0 :+: (Abs tipe $ Pat $ vvar 3 :+: var 0)) 
--         :=: Pat (vvar 3 :+: (Abs tipe $ Pat $ vvar 3 :+: var 0) :+: var 0 :+: (Abs tipe $ Pat $ vvar 2 :+: var 0))
      $ Pat (vvar 3 :+: var 1 :+: var 0 :+: var 2)
         :=: Pat (vvar 3 :+: var 2 :+: var 0 :+: var 1)
     :&: var 0 :=: var 3 -- to view the result!

test2 :: Form
test2 = Bind Forall (tipe ~> tipe ~> tipe) -- 4
      $ Bind Forall (tipe ~> tipe) -- 3
      $ Bind Exists (tipe ~> tipe ~> tipe) -- 2
      $ Bind Forall tipe -- 1
      $ Bind Forall tipe -- 0 
      $ Pat (vvar 2 :+: var 1 :+: var 0) :=: Pat (vvar 3 :+: var 0)
     :&: var 2 :=: var 4 -- to view the result!