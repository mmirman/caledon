{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Src.HOU where

import Src.AST
import Src.Substitution
import Src.Context
import Src.FormulaZipper (Ctxt)

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
        
uvarTy :: Context a => a -> Variable -> Maybe Type
uvarTy ctxt (Exi{}) = Nothing
uvarTy ctxt hB = return $ getTy ctxt hB

gvarTy :: Variable -> Maybe (Int,Name, Type)
gvarTy (hB@(Exi i nm ty) ) = return $ (i,nm, ty)
gvarTy _                   = Nothing

isForall ctxt c = case uvarTy ctxt c of
  Just _  -> True
  _ -> False
  
inj = inj mempty
  where inj m [] = True
        inj m (a:l) = not (S.member a m) && inj (S.insert a m) l

type Reconstruction = M.Map Name (Int {- depth -} , Term {- reconstruction -}) 

substRecon :: (Term,Type, Int, Name, Type) -> Reconstruction -> Reconstruction
substRecon (s , tyB,d, x, tyA) m = M.insert x (d,s) $ fmap substy m
  where substy (depth, t) | depth < d = (depth,t)
        substy (depth, t) = (depth, substN False (emptyCon constants :: Ctxt) (liftV (depth - d) s, tyB, Exi d x tyA) t) 

-- | unify only performes transitions relating to "A :=: B". 
unify :: (Show a, Environment a) => Reconstruction -> a -> Form -> Maybe (Reconstruction, Form)
unify recon ctxt (a :&: b) = case unify recon (putLeft ctxt b) a of
  Nothing -> unify recon (putRight a ctxt) b
  Just a  -> Just a
unify recon ctxt (Bind ty f)    = unify recon (putTy ctxt ty) f
unify recon ctxt Done = Just $ (recon, rebuild ctxt Done)
unify recon na (a :&: b)        = Nothing
unify recon ctxt constraint@(a :=: b) = ueq (a,b) <|> ueq (b,a)
  where len = height ctxt
                  
        ueq (a,b) = case (a,b) of
          (Abs ty n1, n2) -> 
            return ( recon 
                   , rebuild ctxt $ Bind ty $ n1 :=: appN (putTy ctxt ty) (liftV 1 n2) (var 0)
                   )
          (Pat a, Pat b) -> identity a b <|> do
            (hAO,ppA) <- getPP a
            hA <- gvarTy hAO
            let a' = (hA,ppA)
            onlyIf $ partialPerm hAO $ DeBr <$> ppA                                
            gvar_uvar a' b <|> gvar_gvar a' b <|> occurs a' b
          _ -> Nothing
          
        partialPerm hA ppA = all (hA >) ppA && all (isForall ctxt) ppA && inj ppA        
        
        identity h1 h2 | h1 == h2 = return $ (recon, rebuild ctxt Done)
        identity (viewPat -> ~(hAO,ppA)) (viewPat -> ~(hBO, ppB)) = do
          hA <- uvarTy ctxt hAO
          hB <- uvarTy ctxt hBO
          onlyIf $ hA == hB
          if length ppA /= length ppB 
            then error $ "universal quantifiers have different numbers of arguments: "++show constraint 
            else return ()
          return $ ( recon 
                   , rebuild ctxt $ case zipWith (:=:) ppA ppB of
                     [] -> Done
                     lst -> foldr1 (:&:) lst
                   )
        
        gvar_uvar a (viewPat -> ~(hB,mB)) = do
          tyB <- uvarTy ctxt hB
          let b' = (hB, tyB, mB)
          gvar_uvar_outside a b' <|> gvar_uvar_inside a b'

        gvar_gvar a b = do
          (hBO,ppB) <- getPP b
          hB <- gvarTy hBO 
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
              tyB_top = liftV (1 - xVal) tyB -- this is safe since we are at "dist"
              -- we need to up the context by the dist!
          case upI (xVal - 1) ctxt Done of
            Nothing -> 
              return (substRecon (l , tyB_top, dist, xNm , tyB_top) recon, rebuild ctxt Done)
            Just (ctxt,form) -> do
              return $ ( substRecon (l , tyB_top, dist, xNm , tyB_top) recon
                       , rebuild ctxt $ subst ctxt (l,tyB_top, Exi dist xNm tyB_top) $ form 
                       )

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
              
          case upI (xVal - 1) ctxt constraint of
            Nothing -> error $ "we still have a constraint to unify "++show constraint 
            Just (ctxt, form) -> do
              let xVars = (\a -> foldr a [] xNms) $
                          \(xNm,bTy) xs -> (appUVars $
                                            Var $ Exi dist xNm $ foralls $ foldl (appN ctxt) bTy xs
                                           ):xs
                                                                      
                  l = foldr Abs (Pat $ foldl (:+:) (Var hB) xVars) tyLstA
                  
              return $ ( substRecon (l , tyB , dist, xNm, tyA) recon
                       , rebuild ctxt $ subst ctxt (l,tyB, Exi dist xNm tyA) $ form
                       )

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
        raise i (recon, Exi dist xNm tyA, ctx, form) = 
          case upI 1 ctx form of
            Just (ctx'',form') -> let ty = getTy ctx (DeBr 0)
                                      newExi = Exi (dist - 1) (xNm++"@") (forall ty tyA)
                                      newpat = Pat $ (liftV 1 $ Var newExi) :+: var 0 
                                  in  raise (i-1) ( substRecon (newpat, liftV 1 $ tyA, (dist - 1) , xNm, tyA) recon 
                                                  , newExi
                                                  , ctx''
                                                  , liftV (-1) $ subst ctx (newpat,liftV 1 $ tyA, Exi dist xNm tyA) form'
                                                  )
            Nothing -> error $ "can't go this high! "++show i
            
        gvar_gvar_diff (hA@(dist,xNm,tyA),ppA) (hB@(dist',xNm',tyA'),ppB) | dist < dist' =
          case upI (len - dist' - 2) ctxt constraint of
            Just (ctxt,form) -> case raise (dist' - dist) (recon , Exi dist' xNm' tyA', ctxt, form) of
              (recon, _,ctxt,form) -> return $ (recon, rebuild ctxt form)
        gvar_gvar_diff (hA@(dist,_,_),_) (hB@(dist',_,_),_) | dist > dist' = Nothing
        gvar_gvar_diff (hA@(dist,xNm,tyA),ppA) (hB@(dist',xNm',tyB),ppB) | dist == dist' = do
          let xx'Val = len - dist - 1
          case upI (xx'Val) ctxt constraint of
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
              
              return $ ( substRecon (lA, tyA, dist , xNm , tyA) $  
                         substRecon (lB, tyB, dist , xNm', tyB) $ recon
                       , rebuild ctxt $ 
                         subst ctxt (lA, tyA, Exi dist xNm tyA) $ 
                         subst ctxt (lB,tyB, Exi dist xNm' tyA) $ form
                       )

search :: (Show a, Environment a) => Reconstruction -> a -> Form -> Maybe [[(Reconstruction, Form)]]
search recon ctxt (a :&: b) = case search recon (putLeft ctxt b) a of
  Nothing -> search recon (putRight a ctxt) b
  Just a  -> Just a
search recon ctxt (Bind ty f)    = search recon (putTy ctxt ty) f
search recon ctxt Done = Just [[(recon, rebuild ctxt Done)]]
search recon na (a :=: b)        = Nothing
search recon ctxt (a :@: b) = Just $ fmap (\(a,b) -> (a, rebuild ctxt b)) <$> searchR a b
  where searchR search (viewForallN -> Just (a,b)) = 
          [[(recon , Bind a $ y :=: appN (putTy ctxt a) search (var 0) :&: y :@: b) ]]
          where y = evar (height ctxt) "y" b -- y must be NEW!!!
        
        searchL (a,tyA) (b,tyB) = undefined


-- modify all the time, since the only time we mention an existential 
-- is if we are in the same branch, and we know existentials are unique.

unifyAll cons (recon,Done) = return recon
unifyAll cons (recon,unf) = case unify recon (emptyCon cons :: Ctxt) unf of
  Nothing -> error $ "can not unify "++show unf
  Just unf -> unifyAll cons unf
  