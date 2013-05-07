{-# LANGUAGE ViewPatterns                     #-}
{-# LANGUAGE FlexibleContexts                 #-}
{-# LANGUAGE BangPatterns                     #-}
{-# LANGUAGE ScopedTypeVariables              #-}
module Src.HOU (unifyAll) where

import Names
import Src.AST
import Src.Substitution
import Src.Context
import Src.FormulaSequence (Ctxt)
import Src.Variables
import Src.LatticeUnify

import Control.Monad.Trans (lift)

import Control.Monad.State.Class (MonadState())
import Control.Monad.Error.Class (MonadError(..))

import Control.Applicative 
import Data.Monoid
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List

import Control.Monad.Trans.Maybe
import Control.Monad.Identity
import Debug.Trace
import qualified Data.Foldable as F

import System.IO.Unsafe
import Data.IORef

{-# NOINLINE levelVar #-}
levelVar :: IORef Int
levelVar = unsafePerformIO $ newIORef 0

{-# NOINLINE level #-}
level = unsafePerformIO $ readIORef levelVar

vtrace !i | i < level = trace
vtrace _ = const id

vtraceShow _ !i2 s v | i2 < level = trace $ s ++" : "++show v
vtraceShow !i1 _ s _ | i1 < level = trace s
vtraceShow _ _ _ _ = id

throwTrace !i s = vtrace i s $ throwError s

-------------------
--- Combinators ---
-------------------

onlyIf b = if b then return () else nothing

nothing :: Monad m => MaybeT m a
nothing = fail ""

getPP :: Monad m => P -> MaybeT m (Variable, [Int])
getPP p = case bpp p of
  Just (h,pp) -> return (h, pp)
  Nothing -> nothing
  where bpp (p :+: Pat (Var (DeBr v1))) = case bpp p of
          Just (h, pp) -> Just (h, v1:pp)
          Nothing -> Nothing
        bpp (Var h) = Just (h, [])
        bpp (_ :+: _) = Nothing

viewPat p = (h, ml)
  where ~(h,ml) = vp p
        vp (p :+: m) = (h,m:ml)
          where ~(h,ml) = vp p
        vp (Var h) = (h,[])
        
uvarTy :: (Monad m, Context a) => a -> Variable -> MaybeT m Type
uvarTy _ Exi{} = nothing
uvarTy ctxt hB = return $ getTy ctxt hB



gvarTy :: Monad m => Variable -> MaybeT m (Int,Name, Type)
gvarTy (Exi i nm ty) = return $ (i,nm, ty)
gvarTy _             = nothing

isForall ctxt c = case runIdentity $ runMaybeT $ uvarTy ctxt c of
  Just _  -> True
  _ -> False
  
inj = inj mempty
  where inj _ [] = True
        inj m (a:l) = not (S.member a m) && inj (S.insert a m) l

type UniContext = (ConsGraph, Reconstruction)

substRecon :: (Term,Type, Int, Name, Type) -> UniContext -> UniContext
substRecon (s,tyB,d, x, tyA) (gr,m) = (gr, M.insert x (d,s) $ fmap substy m)
  where substy (depth, t,ty) | depth < d = (depth,t)
        substy (depth, t,ty) = (depth, suber t)
          where suber = substN False (emptyCon constants :: Ctxt) (liftV (depth - d) s, tyB, Exi d x tyA)

putGr (gr,recon) foo a b = case foo (con a) (con b) of
  (Pat (Var (Con a))) :=:  (Pat (Var (Con b))) -> do
    gr <- insLTE gr a b
    gr <- insLTE  gr b a
    return (gr,recon)
  (Pat (Var (Con a))) :<:  (Pat (Var (Con b))) -> do
    gr <- insLT gr a b
    return (gr,recon)
  (Pat (Var (Con a))) :<=: (Pat (Var (Con b))) -> do
    gr <- insLTE gr a b
    return (gr,recon)
  _ -> error "can't put this type of constraint into the graph"
  

viewTipe (Var (Con "type") :+: (Pat (Var (Con a)))) = Just a
viewTipe _ = Nothing

viewEquiv (a :=: b) = ((:=:), a, b)
viewEquiv (a :<: b) = ((:<:), a, b)
viewEquiv (a :<=: b) = ((:<=:), a, b)
viewEquiv _ = error "not an equivalence"

-- | unify only performes transitions relating to "A :=: B". 
unify :: (Functor m, Monad m
         , Show a, Environment a
         , MonadError String m
         ) => UniContext -> a -> Form -> MaybeT m (UniContext, Form)
unify recon ctxt (a :&: b) = unify recon (putLeft ctxt b) a 
                            <|> unify recon (putRight a ctxt) b
unify recon ctxt (Bind ty f) = unify recon (putTy ctxt ty) f
unify recon ctxt Done = return $ (recon, rebuild ctxt Done)
unify _ _ (_ :@: _)   = nothing
unify recon ctxt constraint@(viewEquiv -> (f,a,b)) = ueq f (a,b) <|> ueq (flip f) (b,a)
  where len = height ctxt
        
        ueq (=:=) (a,b) = case (a,b) of
          (Abs ty n1, n2) -> 
            return ( recon 
                   , rebuild ctxt $ Bind ty $ n1 =:= appN (putTy ctxt ty) (liftV 1 n2) (var 0)
                   )
          (Pat a, Pat b) -> identity (=:=) a b <|> do
            (hAO,ppA) <- getPP a
            hA <- gvarTy hAO
            let a' = (hA,ppA)
            onlyIf $ partialPerm hAO $ DeBr <$> ppA                                
            gvar_uvar a' b <|> gvar_gvar a' b <|> occurs a' b
          _ -> nothing
          
        partialPerm hA ppA = all (hA >) ppA && all (isForall ctxt) ppA && inj ppA        
        
        identity _ h1 h2 | h1 == h2 = return $ (recon, rebuild ctxt Done)
        identity f (viewTipe -> Just a) (viewTipe -> Just b) = do
          recon <- putGr recon f a b
          return (recon, rebuild ctxt Done)
        identity (=:=) (viewForallP -> Just (a,b)) (viewForallP -> Just (a',b')) = do
          return $ (recon, rebuild ctxt $ a :=: a' :&: b =:= b') -- implements the "switching" for atoms
        identity f (viewPat -> ~(hAO,ppA)) (viewPat -> ~(hBO, ppB)) = do
          hA <- uvarTy ctxt hAO
          hB <- uvarTy ctxt hBO
          onlyIf $ hA == hB
          if length ppA /= length ppB 
            then error $ "universal quantifiers have different numbers of arguments: "++show constraint 
            else return ()
          return $ ( recon 
                   , rebuild ctxt $ case zipWith f ppA ppB of
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
        
        occurs ((dist',xNm',tyB'), _) b = do
          if rigidP (Exi dist' xNm' tyB') b
            then lift $ throwTrace 1 $ "occurs check"
            else nothing
        
        gvar_gvar_same (hA@(_,_,_),ppA) (hB@(dist,xNm,tyB),ppB) = do
          onlyIf $ hA == hB && length ppA == length ppB 
          
          let xNm' = xNm++"@'"
              
              (tyLst,tyBase) = viewN tyB
              
              sames = [ var i | ((a,b),i) <- zip (zip ppA ppB) [0..], a == b ]
                            
              tyB' = getTyLst tyLst (zip ppA ppB)
                where getTyLst (ty:c) ((a,b):lst) | a == b = forall ty $ getTyLst c lst
                      getTyLst (_:c) (_:lst) = liftV (-1) $ getTyLst c lst
                      getTyLst _ _ = Pat $ tyBase
                            
              vlstBase = foldl (:+:) (Var $ Exi dist xNm' tyB') sames
              
              l = foldr Abs (Pat vlstBase) tyLst
              xVal = len - dist - 1
              tyB_top = liftV (1 - xVal) tyB -- this is safe since we are at "dist"
              -- we need to up the context by the dist!
          case upI (xVal) ctxt Done of
            Nothing -> 
              return (substRecon (l , tyB_top, dist, xNm , tyB_top) recon, rebuild ctxt Done)
            Just (ctxt,form) -> do
              return $ ( substRecon (l , tyB_top, dist, xNm , tyB_top) recon
                       , rebuild ctxt $ subst ctxt (l,tyB_top, Exi dist xNm tyB_top) $ form 
                       )

        gvar_fixed (xVal, (dist,xNm,tyA'),_) (hB,tyB',_) = do
              
          let tyA = liftV (1 - xVal) tyA'
              tyB = liftV (1 - xVal) tyB'
              
              ~(tyLstA,_) = viewN tyA
              tyLstB = viewB tyB
                where viewB (viewForallN -> Just (ty,n)) = ty:map (Abs ty) (viewB n)
                      viewB (Pat _) = []
                      viewB Abs{} = error "can't view an abstraction as a forall"
              
              lenTyLstA = length tyLstA
              uVars = var <$> [0..(lenTyLstA - 1)]
              
              appUVars c = Pat $ foldl (:+:) c uVars
              
              foralls base = foldr forall (liftV (lenTyLstA - 1) base) tyLstA
              
              xNms  = [ (xNm++"@"++show i,ty) | (i,ty) <- zip [0..] tyLstB ]
              
          case upI xVal ctxt constraint of
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

        gvar_uvar_outside (hA@(dist,_,_),ppA) (hB,tyB',mB) = do
          let xVal = len - dist - 1
          
          onlyIf $ case hB of
            Con _ -> True
            DeBr yVal -> yVal > xVal
            _ -> False
          gvar_fixed (xVal, hA, ppA) (liftV (length ppA - xVal) hB, tyB', mB)         

        gvar_uvar_inside (hA@(dist,_,_),ppA) (DeBr yVal,tyB',mB) = do
          let xVal = len - dist - 1
          case elemIndex yVal ppA of
            Just hB -> gvar_fixed (xVal, hA, ppA) (DeBr hB, tyB', mB)
            Nothing -> lift $ throwTrace 1 "GVAR-UVAR-DEPENDS"
        gvar_uvar_inside _ _ = nothing
                  
        raise 0 v = v
        raise i (recon, (dist,xNm,tyA), ctx, form) = 
          case upI 1 ctx form of
            Just (ctx'',form') -> let ty = getTy ctx (DeBr 0)
                                      newExi = (dist - 1, xNm++"@", forall ty tyA)
                                      newpat = Pat $ (liftV 1 $ Var $ uncurriedExi newExi) :+: var 0 
                                  in  raise (i-1) ( substRecon (newpat, liftV 1 $ tyA, (dist - 1) , xNm, tyA) recon 
                                                  , newExi
                                                  , ctx''
                                                  , liftV (-1) $ subst ctx (newpat,liftV 1 $ tyA, Exi dist xNm tyA) form'
                                                  )
            Nothing -> error $ "can't go this high! "++show i

          
        gvar_gvar_diff ((dist,_,_),_) ((dist',xNm',tyA'),_) | dist < dist' =
          case upI (len - dist') ctxt constraint of
            Nothing -> error "constraint shouldn't be done"
            Just (ctxt,form) -> case raise (dist' - dist) (recon , (dist',xNm',tyA') , ctxt, form) of
              (recon, _,ctxt,form) -> return $ (recon, rebuild ctxt form)
        gvar_gvar_diff ((dist,_,_),_) ((dist',_,_),_) | dist > dist' = nothing
        gvar_gvar_diff ((dist,xNm,tyA),ppA) ((_,xNm',tyB),ppB) = do
          let xx'Val = len - dist - 1
          case upI xx'Val ctxt constraint of
            Nothing -> error $ "can't go this high! "++show xx'Val
            Just (ctxt, form) -> do
              let xNm'' = xNm++"+"++xNm'++"@"
                  
                  sames = [ (var i, var j) | (a,i) <- zip ppA [0..], (b,j) <- zip ppB [0..], a == b ]
                  
                  (samesA,samesB) = unzip sames
                                    
                  getTyLst tb (ty:c) (a:lst) | elem a ppB = forall ty $ getTyLst tb c lst
                  getTyLst tb (_:c) (_:lst) = liftV (-1) $ getTyLst tb c lst                  
                  getTyLst tb _ _ = Pat $ tb
                  
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

search :: ( Functor m, Show a, Monad m, Environment a
          , MonadState c m, ValueTracker c) =>  a -> Form -> MaybeT m [[Form]]
search ctxt (a :&: b) =  search (putLeft ctxt b) a 
                     <|> search (putRight a ctxt) b
search ctxt (Bind ty f)    = search (putTy ctxt ty) f
search ctxt Done = return [[(rebuild ctxt Done)]]
search _ (_ :=: _)    = nothing
search _ (_ :<: _)    = nothing
search _ (_ :<=: _)   = nothing
search ctxt (a :@: b) = (fmap (rebuild ctxt) <$>) <$> searchR a b
  where searchR search (viewForallN -> Just (a,b)) = do
          yv <- getNewWith "@y"
          let y = evar (height ctxt) yv b
          return $ [[Bind a $ y :=: appN (putTy ctxt a) search (var 0) :&: y :@: b]]
        searchR _ Abs{}   = error "not a type"
        searchR search (Pat p) = do
          let (constants, anons) = getTypes ctxt
              
              pFam = case viewPat p of
                ~(a,_) -> a
                          
              sameFamily s = case getFamily s of
                Poly -> True
                Family s -> s == pFam
                NoFam -> False
              
              makeFromConstant (c,(bl,t)) = if sameFamily t 
                                            then (\a -> Just (bl,a)) <$> searchL (con c, t) (search,p)
                                            else return Nothing
              makeFromAnons (i,t) = if sameFamily t
                                    then (:[]) <$> searchL (var i, t) (search,p)
                                    else return []
                
          cl <- mapM makeFromConstant $ M.toList constants
          rl <- mapM makeFromAnons $ zip [0..] anons
          return $ sortAndUse (catMaybes cl) ++ [ concat rl ]
          
        searchL (name,attempt) tg@(target,goal) = case attempt of
          (viewForallN -> Just (av,b)) -> do
            xv <- getNewWith "@xv"
            let x = evar (height ctxt) xv av
            (:&: x :@: av) <$> searchL (appN ctxt name x, b) tg
          Abs{} -> error "not a type"
          Pat p -> do
            return $ Pat p :=: Pat goal :&: name :=: target

sortAndUse cl = coalate [] $ sortBy (\a b -> compare (snd $ fst a) (snd $ fst b)) cl
  where coalate [] [] = []
        coalate cg [] = [reverse cg]
        coalate cg (((sequ,_),targ):l) = 
          if sequ
          then if not $ null cg 
               then reverse cg:[targ]:coalate [] l
               else [targ]:coalate [] l
          else coalate (targ:cg) l
               
-- modify all the time, since the only time we mention an existential 
-- is if we are in the same branch, and we know existentials are unique.
unifyOrSearch :: (Functor m, Show a, MonadState c m, MonadError String m, Environment a, ValueTracker c) =>
                 UniContext -> a -> Form -> MaybeT m [[(UniContext, Form)]]
unifyOrSearch recon ctxt unf =  tryUnify <|> trySearch
  where tryUnify  = (\a -> [[a]]) <$> unify recon ctxt unf
        trySearch = (((\a -> (recon,a)) <$>) <$>) <$> search ctxt unf

interpret _ (recon, Done) = return recon
interpret cons (recon, unf) = do
  m <- runMaybeT $ unifyOrSearch recon (emptyCon cons :: Ctxt) unf 
  case m of
    Nothing  -> throwTrace 1 $ "constraints are not satisfiable: "++show unf
    Just lst -> next lst
      where next []     = fail "there are no more things to try"
            next (a:l)  = current <|> next l
              where current = interpret cons =<< F.asum (return <$> a)

unifyAll cons unf = snd <$> interpret cons ((newGraph, mempty), unf)