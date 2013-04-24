{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Utwo where

import Control.Applicative 
import Control.Monad
import Data.Maybe
import Data.Functor
import Data.Monoid
import qualified Data.Traversable as T
import qualified Data.Map as M
import qualified Data.Set as S

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
data Variable = DeBr Int 
              | Con Name 
              | Exi Int Name Type -- distance from the top, and type!
              deriving (Eq, Show, Ord)

data P = P :+: N
       | Var Variable
       deriving (Eq, Show, Ord)
                
data N = Abs Type N 
       | Pat P 
       deriving (Eq, Show, Ord)
    
type Term = N
type Type = N

viewForall (Pat (Var (Con "#forall#") :+: _ :+: Abs ty n )) = Just (ty,n)
viewForall _ = Nothing

viewN (viewForall -> Just (ty,n)) = (ty:l,h)
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

constants :: Constants
constants = M.fromList [ (tipeName, tipe)
                       , ("#forall#", forall tipe $ (var 0 ~> tipe) ~> tipe)
                       ]

---------------
--- Formula ---
---------------
infix 2 :&:
infix 3 :=:

data Form = Term :=: Term
          | Form :&: Form
          | Done
          | Bind Type Form
          deriving (Eq, Show)

class Context a where
  getTy :: a -> Variable -> Type
  putTy :: a -> Type -> a
  height :: a -> Int
  
type Constants = M.Map Name Type
type Foralls = [Type]
  
class TERM n where
  -- addAt (amount,thresh) r increases all variables referencing above the threshold down by amount
  addAt :: (Int,Int) -> n -> n
instance TERM P where  
  addAt (amount,thresh) (Var (DeBr a)) = Var $ DeBr $ if a <= thresh then a else amount+a
  addAt i (Var (Exi j nm ty)) = Var $ Exi j nm $ addAt i ty
  addAt _ (Var a) = Var a
  addAt i (p :+: n) = addAt i p :+: addAt i n
instance TERM N where  
  addAt v@(amount,thresh) (Abs ty n) = Abs (addAt v ty) $ addAt (amount, thresh+1) n
  addAt i (Pat p) = Pat $ addAt i p

liftV :: TERM n => Int -> n -> n
liftV v = addAt (v,0) 

liftThree i (a,b,DeBr c) = (liftV i a, liftV i b, DeBr $ i + c)
liftThree i (a,b,Exi j n t) = (liftV i a, liftV i b, Exi j n $ liftV i t)
liftThree i (a,b,c) = (liftV i a, liftV i b, c)

etaExpand :: Type -> P -> N
etaExpand (viewForall -> Just (a,b)) m = Abs a $ Pat $ liftV 1 m :+: etaExpand (liftV 1 a) (vvar 0)
etaExpand _ m = Pat m

substN :: Context c => c -> (Term,Type, Variable) -> N -> N
substN ctxt na (Pat p) = case substP ctxt na p of
  (Right m,p) -> m
  (Left  m,p) -> etaExpand p m
substN ctxt na (Abs b n) = Abs (substN ctxt na b) $ substN (putTy ctxt b) (liftThree 1 na) n

substP :: Context c => c -> (Term,Type, Variable) -> P -> (Either P N, Type)
substP ctxt (n, a, Exi i nm _) (Var (Exi i' nm' _)) | nm == nm' && i == i' = (Right n, a)
substP ctxt (n, a, x') (Var x) | x == x' = (Right n, a)
substP ctxt na (y@(Var v@(Con _))) = (Left y, getTy ctxt v)
substP ctxt na (y@(Var (Exi i nm ty))) = (Left $ Var $ Exi i nm ty', ty')
  where ty' = substN ctxt na ty
substP ctxt na (p :+: n) = hered ctxt (substP ctxt na p) (substN ctxt na n)



hered :: Context c => c -> (Either P N, Type) -> N -> (Either P N, Type)
hered ctxt (Right (Abs a1 n), viewForall -> Just (a1',a2)) nv = 
  ( Right $ substN ctxt (nv,a1,DeBr $ -1) $ addAt (-1,0) n
  , substN ctxt (nv, a1',DeBr $ -1) $ addAt (-1,0) a2
  )
hered ctxt (Right (Pat p1), viewForall -> Just (a1',a2)) nv = 
  ( Right $ Pat (p1 :+: nv)
  , substN ctxt (nv, a1',DeBr $ -1) $ addAt (-1,0) a2
  )
hered ctxt (Left p1, viewForall -> Just (a1',a2)) nv = 
  ( Left $ p1 :+: nv
  , substN ctxt (nv, a1',DeBr $ -1) $ addAt (-1,0) a2
  )

substF :: Context c => c -> (Term,Type,Variable) -> Form -> Form  
substF _ _ Done = Done
substF ctxt sub (a :=: b) = substN ctxt sub a :=: substN ctxt sub b
substF ctxt sub (a :&: b) = substF ctxt sub a :&: substF ctxt sub b
substF ctxt sub (Bind ty f) = Bind (substN ctxt sub ty) $ substF (putTy ctxt ty) (liftThree 1 sub) f

app  :: Context c => c -> Either P N -> N -> Either P N
app ctxt (Right (Abs a1 n)) nv = Right $ substN ctxt (nv,a1,DeBr $ -1) $ addAt (-1,0) n
app ctxt (Right (Pat p1)) nv = Right $ Pat (p1 :+: nv)
app ctxt (Left p1) nv = Left $ p1 :+: nv

appN c p n = case app c (Right p) n of
  Right n -> n
  Left p -> Pat p

instance TERM Form where
  addAt v@(amount,thresh) (Bind ty n) = Bind (addAt v ty) $ addAt (amount, thresh+1) n
  addAt i (p :=: n) = addAt i p :=: addAt i n
  addAt i (p :&: n) = addAt i p :&: addAt i n
  addAt i Done = Done
  
data Ctxt = Top
          | L Ctxt Form 
          | R Form Ctxt 
          | B Ctxt Type
            


type ContCon = (Constants,Int,Ctxt)



emptyCon :: ContCon
emptyCon = (constants, 0, Top)

upZero (L c f) = upZero c
upZero (R f c) = upZero c
upZero t = t

up (L c f) = up c
up (R f c) = up c
up (B c _) = upZero c
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
  B c _ -> upWithZero c Done
  Top -> (Top, Done)
upWith (L c f) ctxt = upWith c $ ctxt :&: f
upWith (R f c) ctxt = upWith c $ f :&: ctxt
upWith (B c ty) ctxt = upWithZero c $ Bind ty ctxt
upWith Top ctxt = (Top, ctxt)

upDone i (a,b) = upDone' i (upWithZero a b)
  where upDone' (-1) (ctxt,Done) = Nothing
        upDone' (-1) (ctxt,nxt)  = Just (ctxt,nxt)
        upDone' i (ctxt,nxt) = upDone' (i-1) (upWith ctxt nxt)


instance Context ContCon where
  getTy (cons,len, _) (Con n) = cons M.! n
  getTy (a,len,c) (DeBr i) = case repeate i up c of
    B _ ty -> ty
  putTy (a,i,c) ty = (a,i+1, B c ty)
  
  height (_,i,_) = i
  
rebuild a Done = rebuildTop a
  where rebuildTop (B c t) = rebuildTop c
        rebuildTop (L c t) = rebuild c t
        rebuildTop (R t c) = rebuild c t
        rebuildTop Top = Done
rebuild (B c t) h = rebuild c $ Bind t h
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
        
uvarTy :: ContCon -> Variable -> Maybe Type
uvarTy ctxt (hB@(DeBr _) ) = return $ getTy ctxt hB
uvarTy _ _ = Nothing

gvarTy :: ContCon -> Variable -> Maybe (Int,Name, Type)
gvarTy ctxt (hB@(Exi i nm ty) ) = return $ (i,nm, ty)
gvarTy _ _                      = Nothing

lft  (cons,len,ctxt) b = (cons, len, L ctxt b)
rght (cons,len,ctxt) b = (cons, len, R b ctxt)

isForall ctxt c = case uvarTy ctxt c of
  Just _  -> True
  _ -> False
  
inj = inj mempty
  where inj m [] = True
        inj m (a:l) = not (S.member a m) && inj (S.insert a m) l



-- | unify only performes transitions relating to "A :=: B". 
unify :: ContCon -> Form -> Maybe Form
unify ctxt (a :&: b) = case unify (lft ctxt b) a of
  Nothing -> unify (rght ctxt a) b
  Just a  -> Just a
unify ctxt (Bind ty f) = unify (putTy ctxt ty) f
unify (cons,len,ctx) Done = Just $ rebuild ctx Done
unify ctxt@(cons,len,ctx) (a :=: b) = ueq (a,b) <|> ueq (b,a)
  where ueq (a,b) = case (a,b) of
          (Abs ty n1, n2) -> Just $ Bind ty $ n1 :=: appN ctxt (liftV 1 n2) (var 0)
          (Pat a, Pat b) -> identity a b <|> do
            (hAO,ppA) <- getPP a
            hA <- gvarTy ctxt hAO
            let a' = (hA,ppA)
            onlyIf $ partialPerm hAO $ DeBr <$> ppA                                
            gvar_uvar a' b <|> gvar_gvar a' b  
          _ -> Nothing
          
        partialPerm hA ppA = all (hA >) ppA && all (isForall ctxt) ppA && inj ppA        
        
        identity h1 h2 | h1 == h2 = return Done
        identity _  _ = Nothing

        gvar_uvar a b = do
          let (hB,mB) = viewPat b
          tyB <- uvarTy ctxt hB
          let b' = (hB, tyB, mB)
          gvar_uvar_outside a b' <|> gvar_uvar_inside a b'

        gvar_gvar a b = do
          (hBO,ppB) <- getPP b
          hB <- gvarTy ctxt hBO 
          let b' = (hB,ppB)
          onlyIf $ partialPerm hBO $ DeBr <$> ppB              
          gvar_gvar_same a b' <|> gvar_gvar_diff a b'

        gvar_gvar_same (hA,ppA) (hB@(dist,nm,tyB),ppB) = do
          onlyIf $ hA == hB
                && length ppA == length ppB
                
          let (tyLst,tyBase) = viewN tyB
              
              sames = [ i | ((a,b),i) <- zip (zip ppA ppB) [0..], a == b ]
              
              mapping = M.fromList $ zip sames [0..]
              
              vLst = [ var $ fromMaybe 0 $ M.lookup i mapping | (_,i) <- zip ppA [0..] ]
              
              tyB' = getTyLst tyLst (zip ppA ppB)
                where getTyLst [] [] = Pat $ tyBase
                      getTyLst (ty:c) ((a,b):lst) | a == b = forall ty $ getTyLst c lst
                      getTyLst (ty:c) (_:lst) = liftV (-1) $ getTyLst c lst
              
              vlstBase = foldl (:+:) (Var $ Exi dist nm tyB') vLst
              
              l = foldr Abs (Pat vlstBase) tyLst
              upMove = height ctxt - dist
              -- we need to up the context by the dist!
          case upDone upMove (ctx,Done) of
            Nothing -> return $ rebuild ctx Done
            Just (ctxt, form) -> do
              let tyB_top = liftV (-upMove) tyB -- this is safe since we are at "dist"
              return $ rebuild ctxt $ substF (cons, dist, ctxt) (l,tyB_top, Exi dist nm tyB_top) $ form
        
        gvar_uvar_inside  (hA,ppA) (hB,tyB,mB)  = undefined
        
        gvar_uvar_outside (hA,ppA) (hB,tyB,mB)  = undefined        
        
        gvar_gvar_diff    (hA,ppA) (hB,ppB) = undefined



evvar :: Int -> Name -> Type -> P
evvar i n t = Var $ Exi i n t

evar :: Int -> Name -> Type -> N
evar i n t = Pat $ Var $ Exi i n t

ttt = tipe ~> tipe ~> tipe
tttt = tipe ~> ttt

test3 :: Form
test3 = Bind tipe -- 2
      $ Bind tipe -- 1 
      $ Bind tipe -- 0 
      $ Pat (evvar 0 "a" tttt :+: var 1 :+: var 0 :+: var 2) :=: Pat (vvar 3 :+: var 2 :+: var 0 :+: var 1)
     :&: var 0 :=: evar 0 "a" tttt -- to view the result!

test2 :: Form
test2 = Bind ttt -- 3
      $ Bind (tipe ~> tipe) -- 2
      $ Bind tipe -- 1
      $ Bind tipe -- 0 
      $ Pat (evvar 2 "a" ttt :+: var 1 :+: var 0) :=: Pat (vvar 3 :+: var 0)
     :&: var 2 :=: evar 2 "a" ttt -- to view the result!