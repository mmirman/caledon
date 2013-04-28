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
import Data.List

import Debug.Trace
import Control.DeepSeq
import Control.Spoon

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
              deriving (Eq,Ord)

data P = P :+: N
       | Var Variable
       deriving (Eq, Ord)
                
data N = Abs Type N 
       | Pat P 
       deriving (Eq, Ord)
    
instance Show Variable where
  show (DeBr i) = show i
  show (Exi i n ty) = n++"<"++show i++">" -- "("++n++"<"++show i++">:"++show ty++")"
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

viewForallN (Pat p) = viewForallP p
viewForallN _ = Nothing

viewForallP (Var (Con "#forall#") :+: _ :+: Abs ty n ) = Just (ty,n)
viewForallP _ = Nothing

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
infixr 2 :&:
infix 3 :=:

data Form = Term :=: Term
          | Form :&: Form
          | Done
          | Bind Type Form
          deriving Eq

instance Show Form where
  show (t1 :=: t2) = show t1 ++ " ≐ "++ show t2
  show (t1 :&: t2) = " ( "++show t1 ++ " ) ∧ ( "++ show t2++" )"
  show (Bind t1 t2) = " ∀: "++ show t1 ++ " . "++show t2
  show Done = " ⊤ "

instance NFData Form where
  rnf a = rnf $ show a

class Context a where
  getTy :: a -> Variable -> Type
  putTy :: a -> Type -> a
  height :: a -> Int
  
type Constants = M.Map Name Type
type Foralls = [Type]
  
class TERM n where
  -- addAt (amount,thresh) r increases all variables referencing above the threshold down by amount
  addAt :: (Int,Int) -> n -> n
  
instance TERM Variable where  
  addAt (amount,thresh) (DeBr a) = DeBr $ if a <= thresh then a else amount+a
  addAt i (Exi j nm ty) = Exi j nm $ addAt i ty
  addAt _ a = a
  
instance TERM P where  
  addAt i (Var a) = Var $ addAt i a
  addAt i (p :+: n) = addAt i p :+: addAt i n
instance TERM N where  
  addAt v@(amount,thresh) (Abs ty n) = Abs (addAt v ty) $ addAt (amount, thresh+1) n
  addAt i (Pat p) = Pat $ addAt i p

liftV :: TERM n => Int -> n -> n
liftV v = addAt (v,-1) 

liftThree i (a,b,DeBr c) = (liftV i a, liftV i b, DeBr $ i + c)
liftThree i (a,b,Exi j n t) = (liftV i a, liftV i b, Exi j n $ liftV i t)
liftThree i (a,b,c) = (liftV i a, liftV i b, c)

etaExpand :: Type -> P -> N
etaExpand (viewForallN -> Just (a,b)) m = 
  -- only eta expand heads and not arguments since we need arguments in eta reduced form for type checking!
  Abs a $ Pat $ (liftV 1 m) :+: var 0 -- etaExpand (liftV 1 a) (vvar 0)
etaExpand _ m = Pat m

substN :: Context c => Bool -> c -> (Term,Type, Variable) -> N -> N
substN t ctxt na (Pat p) = case substP t ctxt na p of
  (Right m,p) -> m
  (Left  m,p) -> if t then etaExpand p m else Pat m
substN t ctxt na (Abs b n) = 
  -- don't bother eta-expanding types, just patterns
  Abs (substN False ctxt na b) $ substN t (putTy ctxt b) (liftThree 1 na) n

substP :: Context c => Bool -> c -> (Term,Type, Variable) -> P -> (Either P N, Type)
substP t ctxt sub@(n, a, Exi i nm _) targ@(Var (Exi i' nm' _)) | nm == nm' = 
  if i == i' 
  then (Right n, a) 
  else error $ "these should be the same depth! ["++show sub++"] "++show targ
substP t ctxt (n, a, x') (Var x) | x == x' = (Right n, a)
substP t ctxt na (y@(Var (Exi i nm ty))) = (Left $ Var $ Exi i nm ty', ty')
  where ty' = substN False ctxt na ty
substP t ctxt na (y@(Var v)) = (Left y, getTy ctxt v)
substP t ctxt na (p :+: n) = 
  -- only eta expand heads and not arguments!
  hered t ctxt (substP t ctxt na p) (substN False ctxt na n)

hered :: Context c => Bool -> c -> (Either P N, Type) -> N -> (Either P N, Type)
hered t ctxt (Right p1@(Abs a1 n), l) nv = 
  ( Right $ liftV (-1) $ substN t (putTy ctxt a1) (liftV 1 nv,liftV 1 a1,DeBr 0) n
  , case viewForallN l of 
    Just ~(a1',a2) -> liftV (-1) $ substN False (putTy ctxt a1') (liftV 1 nv,liftV 1 a1',DeBr 0) a2
    Nothing -> error $ show p1++" r: "++show l
  )
hered t ctxt (Right (Pat p1), l) nv = 
  ( Right $ Pat $ p1 :+: nv
  , case viewForallN l of
     Just ~(a1',a2) -> liftV (-1) $ substN False (putTy ctxt a1') (liftV 1 nv, liftV 1 a1',DeBr 0) a2
     Nothing -> error $ show p1++" r: "++show l
  )
hered t ctxt (Left p1, l) nv = 
  ( Left $ p1 :+: nv
  , case viewForallN l of
    Just ~(a1',a2) -> liftV (-1) $ substN False (putTy ctxt a1') (liftV 1 nv, liftV 1 a1',DeBr 0) a2
    Nothing -> error $ show p1++" l: "++show l
  )


substF :: Context c => c -> (Term,Type,Variable) -> Form -> Form  
substF _ _ Done = Done
substF ctxt sub (a :=: b) = substN True ctxt sub a :=: substN True ctxt sub b
substF ctxt sub (a :&: b) = substF ctxt sub a :&: substF ctxt sub b
substF ctxt sub (Bind ty f) = Bind (substN True ctxt sub ty) $ substF (putTy ctxt ty) (liftThree 1 sub) f

subst c s f = case spoon (substF c s f) of
  Nothing -> error $ "SUBST: ["++show s++" ] " ++ show f ++ "\nCTXT: "++show c
  Just a  -> a


app  :: Context c => c -> Either P N -> N -> Either P N
app ctxt (Right (Abs a1 n)) nv = Right $ liftV (-1) $ substN True (putTy ctxt a1) (liftV 1 nv,liftV 1 a1,DeBr 0) n
app ctxt (Right (Pat p1)) nv = Right $ Pat (p1 :+: nv)
app ctxt (Left p1) nv = Left $ p1 :+: nv

appN :: Context c => c -> N -> N -> N
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
          deriving (Show)


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
  getTy (cons,len, _) (Exi i nm ty) = ty
  getTy (a,len,c) (DeBr i) = case repeate i up $ upZero c of
    B _ ty -> liftV i $ ty
    Top -> error $ "WHAT? "++show i++"\nIN: "++show c
    
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

viewPat p = Just (h, ml)
  where ~(h,ml) = vp p
        vp (p :+: m) = (h,m:ml)
          where ~(h,ml) = vp p
        vp (Var h) = (h,[])
        
uvarTy :: ContCon -> Variable -> Maybe Type
uvarTy ctxt (hB@(DeBr _) ) = return $ getTy ctxt hB
uvarTy (cons,_,_) (Con c) = M.lookup c cons
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
unify ctxt@(cons,len,ctx) constraint@(a :=: b) = ueq (a,b) <|> ueq (b,a)
  where ueq (a,b) = case (a,b) of
          (Abs ty n1, n2) -> Just $ rebuild ctx $ Bind ty $ n1 :=: appN (putTy ctxt ty) (liftV 1 n2) (var 0)
          (Pat a, Pat b) -> identity a b <|> do
            (hAO,ppA) <- getPP a
            hA <- gvarTy ctxt hAO
            let a' = (hA,ppA)
            onlyIf $ partialPerm hAO $ DeBr <$> ppA                                
            gvar_uvar a' b <|> gvar_gvar a' b <|> occurs a' b
          _ -> Nothing
          
        partialPerm hA ppA = all (hA >) ppA && all (isForall ctxt) ppA && inj ppA        
        
        identity h1 h2 | h1 == h2 = return $ rebuild ctx Done
        identity a b = do
          (hAO, ppA) <- viewPat a
          (hBO, ppB) <- viewPat b
          hA <- uvarTy ctxt hAO
          hB <- uvarTy ctxt hBO
          onlyIf $ hA == hB
          if length ppA /= length ppB 
            then error $ "universal quantifiers have different numbers of arguments: "++show constraint 
            else return ()
          return $ rebuild ctx $ case zipWith (:=:) ppA ppB of
            [] -> Done
            lst -> foldr1 (:&:) lst
        
        gvar_uvar a b = do
          (hB,mB) <- viewPat b
          tyB <- uvarTy ctxt hB
          let b' = (hB, tyB, mB)
          gvar_uvar_outside a b' <|> gvar_uvar_inside a b'

        gvar_gvar a b = do
          (hBO,ppB) <- getPP b
          hB <- gvarTy ctxt hBO 
          let b' = (hB,ppB)
          onlyIf $ partialPerm hBO $ DeBr <$> ppB              
          gvar_gvar_same a b' <|> gvar_gvar_diff a b'
        
        rigidP x (var :+: p) = rigidP x var || rigid x p
        rigidP x (Var v) = v == x
        
        rigid x (Abs ty m) = rigid x ty || rigid (liftV 1 x) m
        rigid x (Pat p) = rigidP x p
        
        occurs (hA@(dist',xNm',tyB'), ppA) b = do
          if rigidP (Exi dist' xNm' tyB') b
            then error $ "occurs check"
            else Nothing
        
        gvar_gvar_same (hA@(dist',xNm',tyB'),ppA) (hB@(dist,xNm,tyB),ppB) = do
          onlyIf $ hA == hB && length ppA == length ppB 
          
          let xNm' = xNm++"@'"
              
              (tyLst,tyBase) = viewN tyB
              
              sames = [ var i | ((a,b),i) <- zip (zip ppA ppB) [0..], a == b ]
                            
              tyB' = getTyLst tyLst (zip ppA ppB)
                where getTyLst [] [] = Pat $ tyBase
                      getTyLst (ty:c) ((a,b):lst) | a == b = forall ty $ getTyLst c lst
                      getTyLst (ty:c) (_:lst) = liftV (-1) $ getTyLst c lst
              
              (tyLst',tyBase') = viewN tyB'
              
              vlstBase = foldl (:+:) (Var $ Exi dist xNm' tyB') sames
              
              l = foldr Abs (Pat vlstBase) tyLst
              xVal = len - dist - 1
              -- we need to up the context by the dist!
          case upDone (xVal - 1)  (ctx,Done) of
            Nothing -> return $ rebuild ctx Done
            Just (ctxt, form) -> do
              let tyB_top = liftV (1 - xVal) tyB -- this is safe since we are at "dist"
              return $ rebuild ctxt $ subst (cons, dist, ctxt) (l,tyB_top, Exi dist xNm tyB_top) $ form

        gvar_fixed (xVal, hA@(dist,xNm,tyA'),ppA) (hB,tyB',mB) = do
              
          let tyA = liftV (1 - xVal) tyA'
              tyB = liftV (1 - xVal) tyB'
              
              
              (tyLstA,tyBaseA) = viewN tyA
              tyLstB = viewB tyB
                where viewB (viewForallN -> Just (ty,n)) = ty:map (Abs ty) (viewB n)
                      viewB (Pat p) = []
              
              lenTyLstA = length tyLstA
              uVars = var <$> [0..(lenTyLstA - 1)]
              
              appUVars c = Pat $ foldl (:+:) c uVars
              
              foralls base = foldr forall (liftV (lenTyLstA - 1) base) tyLstA
              
              xNms  = [ (xNm++"@"++show i,ty) | (i,ty) <- zip [0..] tyLstB ]
              
          case upDone (xVal - 1) (ctx,constraint) of
            Nothing -> error $ "we still have a constraint to unify "++show constraint 
            Just (ctxt, form) -> do
              let xVars = (\a -> foldr a [] xNms) $
                          \(xNm,bTy) xs -> (appUVars $
                                            Var $ Exi dist xNm $ foralls $ foldl (appN (cons,dist,ctxt)) bTy xs
                                           ):xs
                                                                      
                  l = foldr Abs (Pat $ foldl (:+:) (Var hB) xVars) tyLstA
                  
              return $ rebuild ctxt $ subst (cons, dist, ctxt) (l,tyB, Exi dist xNm tyA) $ form

        gvar_uvar_outside (hA@(dist,xNm,tyA'),ppA) (hB,tyB',mB) = do
          let xVal = len - dist - 1
          
          onlyIf $ case hB of
            Con _ -> True
            DeBr yVal -> yVal > xVal
          gvar_fixed (xVal, hA, ppA) (liftV (length ppA - xVal) hB, tyB', mB)         

        gvar_uvar_inside (hA@(dist,xNm,tyA'),ppA) (DeBr yVal,tyB',mB) = do
          let xVal = len - dist - 1
          case elemIndex yVal ppA of
            Just hB -> gvar_fixed (xVal, hA, ppA) (DeBr hB, tyB', mB)
            Nothing -> error "GVAR-UVAR-DEPENDS"
        gvar_uvar_inside _ _ = Nothing
                  
        raise 0 v = v
        raise i (Exi dist xNm tyA, (cons,len,ctxt'), form) = 
          case upDone 1 (ctxt',form) of
            Just (ctxt'',form') -> let ty = getTy (cons,len,ctxt') (DeBr 0)
                                       newExi = Exi (dist - 1) (xNm++"@") (forall ty tyA)
                                   in  raise (i-1) (newExi, (cons,len - 1, ctxt''), liftV (-1) $ subst (cons,len, ctxt') (Pat $ (liftV 1 $ Var newExi) :+: var 0 ,liftV 1 $ tyA, Exi dist xNm tyA) form')
            Nothing -> error $ "can't go this high! "++show i
            
        gvar_gvar_diff (hA@(dist,xNm,tyA),ppA) (hB@(dist',xNm',tyA'),ppB) | dist < dist' =
          case upDone (len - dist' - 2) (ctx,constraint) of
            Just (ctxt,form) -> case raise (dist' - dist) (Exi dist' xNm' tyA', (cons,dist',ctxt), form) of
              (_,(_,_,ctxt),form) -> return $ rebuild ctxt form
        gvar_gvar_diff (hA@(dist,_,_),_) (hB@(dist',_,_),_) | dist > dist' = Nothing
        gvar_gvar_diff (hA@(dist,xNm,tyA),ppA) (hB@(dist',xNm',tyB),ppB) | dist == dist' = do
          let xx'Val = len - dist - 1
          case upDone (xx'Val) (ctx, constraint) of
            Nothing -> error $ "can't go this high! "++show xx'Val
            Just (ctxt, form) -> do
              let xNm'' = xNm++"+"++xNm'++"@"
                  xVal = len - dist - 1              
                  
                  
                  sames = [ (var i, var j) | (a,i) <- zip ppA [0..], (b,j) <- zip ppB [0..], a == b ]
                  
                  (samesA,samesB) = unzip sames
                                    
                            
                  getTyLst tb [] [] = Pat $ tb
                  getTyLst tb (ty:c) (a:lst) | elem a ppB = forall ty $ getTyLst tb c lst
                  getTyLst tb (ty:c) (_:lst) = liftV (-1) $ getTyLst tb c lst                  
                  
                  (tyLstA,tyBaseA) = viewN tyA
                  (tyLstB,_) = viewN tyB
                  
                  tyX' = getTyLst tyBaseA tyLstA ppA
              
                  vlstBaseA = foldl (:+:) (Var $ Exi dist xNm'' tyX') samesA
                  vlstBaseB = foldl (:+:) (Var $ Exi dist xNm'' tyX') samesB
                  
                  lA = foldr Abs (Pat vlstBaseA) tyLstA
                  lB = foldr Abs (Pat vlstBaseB) tyLstB

              return $ rebuild ctxt $ 
                subst (cons, dist, ctxt) (lA, tyA, Exi dist xNm tyA) $ 
                subst (cons, dist, ctxt) (lB,tyB, Exi dist xNm' tyA) $ form

type Reconstruction = M.Map Name (Int {- depth -} , Term {- reconstruction -}) 
-- modify all the time, since the only time we mention an existential 
-- is if we are in the same branch, and we know existentials are unique.

evvar :: Int -> Name -> Type -> P
evvar i n t = Var $ Exi i n t

evar :: Int -> Name -> Type -> N
evar i n t = Pat $ Var $ Exi i n t


tt = tipe ~> tipe
ttt = tipe ~> tt
tttt = tipe ~> ttt

test3 :: Form
test3 = Bind tipe -- 2
      $ Bind tipe -- 1 
      $ Bind tipe -- 0 
      $ Pat (evvar 0 "a" tttt :+: var 1 :+: var 0 :+: var 2) :=: Pat (evvar 0 "a" tttt :+: var 2 :+: var 0 :+: var 1)
     :&: evar 1 "n" tttt :=: evar 0 "a" tttt -- to view the result!

test2 :: Form
test2 = Bind ttt  -- 3
      $ Bind tt   -- 2
      $ Bind tipe -- 1
      $ Bind tipe -- 0 
      $ Pat (evvar 2 "a" ttt :+: var 1 :+: var 0) :=: Pat (vvar 2 :+: var 0)
     :&: evar 3 "g" ttt :=: evar 2 "a" ttt -- to view the result!

test1 :: Form
test1 = Bind tt   -- 2
      $ Bind tipe -- 1
      $ Bind tipe -- 0 
      $ Pat (evvar 2 "a" ttt :+: var 1 :+: var 0) :=: var 1
     :&: evar 3 "z" ttt :=: evar 2 "a" ttt -- to view the result!

testN :: Form
testN = Bind tipe
      $ Bind tipe
      $ Pat (evvar 0 "z" ttt :+: var 1 :+: var 0) :=: Pat (evvar 1 "x" tt :+: var 0)
      
testN1 :: Form
testN1 = Bind tipe
       $ Bind tipe
       $ Pat (evvar 0 "z" ttt :+: var 1 :+: var 0) :=: Pat (evvar 0 "x@" ttt :+: var 1 :+: var 0)      
      :&: evar 0 "x@" ttt :=: evar 0 "x@" ttt
       
testN1p :: Form
testN1p = Bind tipe
        $ Bind tipe
        $ Pat (evvar 0 "z" ttt :+: var 1 :+: var 0) :=: Pat (evvar 0 "x@" tt :+: var 0)      
       :&: evar 0 "z" ttt :=: evar 1 "arg" ttt
       :&: evar 1 "zola" tt :=: evar 0 "x@" tt
        
unifyAll Done = return ()
unifyAll unf = case unify emptyCon unf of
  Nothing -> error $ "can not unify "++show unf
  Just unf -> unifyAll unf
  