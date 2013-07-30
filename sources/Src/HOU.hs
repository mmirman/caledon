{-# LANGUAGE ViewPatterns                     #-}
{-# LANGUAGE FlexibleContexts                 #-}
{-# LANGUAGE BangPatterns                     #-}
{-# LANGUAGE ScopedTypeVariables              #-}
module Src.HOU (unifyAll, newGraph, ConsGraph) where



import Choice
import Names
import Src.AST
import Src.Substitution
import Src.Context
import Src.FormulaSequence (Ctxt)
import Src.Variables
import Src.LatticeUnify
import Src.Tracing

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



throwTrace !i s = vtrace i s $ throwError s

-------------------
--- Combinators ---
-------------------

onlyIf b = if b then return () else nothing

nothing :: Monad m => MaybeT m a
nothing = fail " nothing "
 
getPP :: Monad m => P -> MaybeT m (Variable, [Int])
getPP p = case bpp p of
  Just (h,pp) -> return (h, pp)
  Nothing -> nothing
  where bpp (p :+: (etaReduce -> Pat (Var (DeBr v1)))) = case bpp p of
          Just (h, pp) -> Just (h, v1:pp)
          Nothing -> Nothing
        bpp (Var h) = Just (h, [])
        bpp (_ :+: _) = Nothing

viewPat p = (h, ml)
  where ~(h,ml) = vp p
        vp (p :+: m) = (h,m:ml)
          where ~(h,ml) = vp p
        vp (Var h) = (h,[])

viewTy [] p = ([],p)
viewTy (arg:lst) (viewForallP -> Just ~(ty,n)) = (ty:l,h)
  where ~(l,h) = viewTy lst n
viewTy _ p = ([],p)

viewTyArgs ctxt [] p = []
viewTyArgs ctxt (arg:l) (viewForallP -> Just ~(ty,n)) = 
  ty:viewTyArgs ctxt l n -- (fromType $ appP' (Abs ty $ Pat n) $ Var $ DeBr arg)
viewTyArgs ctxt l p = map (getTy ctxt . DeBr) l


uvarTy recon _ Exi{} = nothing

uvarTy recon ctxt (Con "#forall#") = do
  v1 <- getNewWith "@v1"
  v2 <- getNewWith "@v2"
  v3 <- getNewWith "@v3"
  recon <- putGr recon (:<=:) v1 v3
  recon <- putGr recon (:<=:) v2 v3
  return $ (forall (tipemake v1) $ (vvar 0 ~> tipemake v2) ~> tipemake v3, recon)
uvarTy recon ctxt hB = return $ (getTy ctxt hB, recon)



gvarTy :: Monad m => Variable -> MaybeT m (Int,Name, Type)
gvarTy (Exi i nm ty) = return $ (i,nm, ty)
gvarTy _             = nothing

isForall ctxt Exi{} = False
isForall ctxt c = True
  
inj :: Ord a => [a] -> Bool  
inj = inj mempty
  where inj _ [] = True
        inj m (a:l) = not (S.member a m) && inj (S.insert a m) l

type UniContext = (ConsGraph, Reconstruction)

substRecon :: (Term,Int, Name) -> UniContext -> UniContext
substRecon (s,d, x) (gr,m) = (gr, M.insert x (d,s) $ fmap substy m)
  where substy (depth,t) | depth < d = (depth,t)
        substy (depth,t) = (depth, suber t)
          where suber = substN' (liftV (depth - d) s, Exi d x undefined)

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
  
-- | unify only performes transitions relating to "A :=: B". 
unify :: (Functor m, Monad m
         , Show a, Environment a
         , MonadError String m
         , MonadState Int m
         ) => UniContext -> (a,Form) -> MaybeT m (UniContext, (a,Form))
unify recon (ctxt,a :&: b) = unify recon (putLeft ctxt b, a )
                          <|> unify recon (putRight a ctxt, b)
unify recon (ctxt,Bind ty f) = unify recon (putTy ctxt ty, f)
unify recon (ctxt,Done) = nothing -- return $ (recon, reset ctxt Done)
unify _ (_,_ :@: _)   = nothing
unify recon (ctxt, constraint@(viewEquiv -> (f,a,b))) = ueq f (a,b) <|> ueq (flip f) (b,a)
  where len = height ctxt
        
        ueq (=:=) (a,b) = case (a,b) of
          (Abs ty1 n1, Abs ty2 n2) -> vtrace 4 "*abs*" $ 
            return ( recon 
                   , reset ctxt $ Pat ty1 :=: Pat ty2 :&: (Bind ty2 $ n1 =:= n2)
                   )

          (Abs ty n1, n2) -> vtrace 4 "*abs*" $ 
            return ( recon 
                   , reset ctxt $ Bind ty $ n1 =:= appN (putTy ctxt ty) (liftV 1 n2) (var 0)
                   )
            
          (Pat a, Pat b) -> identity (=:=) a b <|> do
            (hAO,ppA) <- getPP a
            hA <- gvarTy hAO
            let a' = (hA,ppA)
            onlyIf $ partialPerm hAO ppA                                
            gvar_uvar a' b <|> gvar_gvar a' b <|> occurs a' b
          _ -> nothing
          
        partialPerm hA ppA = case hA of
          DeBr i -> all (i >) ppA && inj ppA
          _ -> inj ppA
        
        identity _ h1 h2 | h1 == h2 = return $ (recon, reset ctxt Done)
        identity f (universeView -> Init a) (universeView -> Init b) = do
          recon <- putGr recon f a b
          return (recon, reset ctxt Done)
        identity f (tipeView -> Init a) (tipeView -> UniversalType) = do
          return (recon, reset ctxt Done)
        identity f (tipeView -> UniversalType) (tipeView -> Init a) = do
          return (recon, reset ctxt Done)
        identity (=:=) (viewForallPsimp -> Just (a,b)) (viewForallPsimp -> Just (a',b')) = do
          return $ (recon, reset ctxt $ Pat a :=: Pat a' :&: b =:= b') -- implements the "switching" for atoms
        identity f (viewPat -> ~(hAO,ppA)) (viewPat -> ~(hBO, ppB)) = do
          (hA,recon) <- uvarTy recon ctxt hAO
          (hB,recon) <- uvarTy recon ctxt hBO
          onlyIf $ hA == hB
          if length ppA /= length ppB 
            then error $ "universal quantifiers have different numbers of arguments: "++show constraint 
            else return ()
          return $ ( recon 
                   , reset ctxt $ case zipWith f ppA ppB of
                     [] -> Done
                     lst -> foldr1 (:&:) lst
                   )
        
        gvar_uvar a (viewPat -> ~(hB,mB)) = do
          (tyB,recon) <- uvarTy recon ctxt hB
          let b' = (hB, tyB, mB)
          gvar_uvar_outside recon a b' <|> gvar_uvar_inside recon a b'

        gvar_gvar a b = do
          (hBO,ppB) <- getPP b
          hB <- gvarTy hBO 
          let b' = (hB,ppB)
          onlyIf $ partialPerm hBO ppB              
          gvar_gvar_same a b' <|> gvar_gvar_diff a b'
        
        rigidP x (var :+: p) = rigidP x var || rigid x p
        rigidP x (Var v) = v == x
        
        rigid x (Abs ty m) = rigidP x ty || rigid (liftV 1 x) m
        rigid x (Pat p) = rigidP x p
        
        occurs ((dist',xNm',tyB'), _) b = do
          if rigidP (Exi dist' xNm' tyB') b
            then lift $ throwTrace 1 $ "occurs check"
            else nothing
        
        gvar_gvar_same (hA@(_,_,_),ppA) (hB@(dist,xNm,tyB),ppB) = do
          onlyIf $ hA == hB && length ppA == length ppB 
          
          vtrace 4 "*gvar_gvar_same*" $ return ()
          
          let xNm' = xNm++"@'"
              
              (tyLst,tyBase) = viewP tyB
              
              sames = [ var i | ((a,b),i) <- zip (zip ppA ppB) [0..], a == b ]
                            
              tyB' = getTyLst tyLst (zip ppA ppB)
                where getTyLst (ty:c) ((a,b):lst) | a == b = forall ty $ getTyLst c lst
                      getTyLst (_:c) (_:lst) = liftV (-1) $ getTyLst c lst
                      getTyLst _ _ = tyBase
                            
              vlstBase = foldl (:+:) (Var $ Exi dist xNm' tyB') sames
              
              l = foldr Abs (Pat vlstBase) tyLst
              xVal = len - dist
              tyB_top = liftV (- xVal) tyB -- this is safe since we are at "dist"
              -- we need to up the context by the dist!
          case upI xVal ctxt Done of
            Nothing -> 
              return (substRecon (l , dist, xNm) recon, reset ctxt Done)
            Just (ctxt,form) -> do
              return $ ( substRecon (l , dist, xNm) recon
                       , reset ctxt $ subst' (l, Exi dist xNm tyB_top) $ form 
                       )
        
        
        gvar_fixed isIn recon (xVal, (dist,xNm,tyA'),ppA) (hB,tyB',mB) = do
          let tyA = liftV (- xVal) tyA'
              
              viewTyArgs _ (viewHead -> Exi{} ) = nothing -- always solve the type first (as much as needed), then solve the value!
              viewTyArgs [] p = return []
              viewTyArgs (arg:l) (viewForallP -> Just ~(ty,n)) = do
                l' <- viewTyArgs l n
                return $ ty:l'

              viewTyArgs args p = nothing
                                  
              viewTyArgs _ (viewHead -> Exi{} ) = nothing -- always solve the type first (as much as needed), then solve the value!
              viewB [] _ = return []
              viewB (_:l) (viewForallP -> Just ~(ty,n)) = do
                v <- viewB l n
                return $ Pat ty:map (Abs ty) v
              viewB _ _ = nothing
          tyLstA <- viewTyArgs ppA tyA
          
          let lenTyLstA = length tyLstA
              tyB = if isIn 
                    then case hB of
                      DeBr hB -> liftV fromTop $ addAt (lenTyLstA, fromTop - 1) $ lst !! fromTop
                        where lst = fst (viewP tyA)
                              ll = length lst
                              fromTop = ll - hB - 1
                    else liftV (- xVal) tyB'
          tyLstB <- viewB mB tyB -- need to seperate out the "outside variables (outside of the gvar)" from the inside variables, and lift only the out //63@fbody^1\^0\.  
                      
          let uVars = reverse $ var <$> [0..(lenTyLstA - 1)]
              
              appUVars c = foldl (:+:) c uVars
              
              foralls base = liftV lenTyLstA $ foldr forall base tyLstA  -- we raise after quantifying because we are capturing base with tyLstA
              
              xNms = [ ("/"++xNm++"^"++show i++"\\",ty) | (i,ty) <- zip [0..] tyLstB ]
              
          case upI xVal ctxt constraint of
            Nothing -> error $ "we still have a constraint to unify "++show constraint 
            Just (ctxt, form) -> do
              let xVars [] = []                     
                  xVars ((xNm,bTy):xNms) = 
                    (appUVars $ Var $ Exi dist xNm $ foralls $ fromType $ foldl appP' bTy $ reverse xs):xs
                    where xs = xVars xNms

                  xVar = reverse $ xVars $ reverse xNms
                  l = foldr Abs (Pat $ foldl (:+:) (Var hB) $ Pat <$> xVar) tyLstA

              True <- return $ deepAppendError ( "CHECK_EXI_TOP: ****" 
                                               ++"\nWITH:  "++show tyLstA
                                               ++"\nFOR: "++show tyA
                                               ++"\nXA: "++show (Exi dist xNm tyA)
                                               ++"\nTYB: "++show tyB
                                               ++"\nPPA: "++show ppA
                                               ++"\nMB: "++show mB
                                               ++"\nL: "++show l
                                               ++"\nCONSTRAINT: "++show constraint
                                               ++"\nFORM: "++show (rebuild ctxt constraint)
                                               ) $ checkExiTop (height ctxt) l
              
              vtrace 6 ("L: "++show l) $ 
                vtrace 6 ("TYLSTB: "++show tyLstB) $               
                vtrace 6 ("TYB: "++show tyB) $
                vtrace 6 ("TYB': "++show tyB') $
                vtrace 6 ("TYA: "++show tyA) $
                vtrace 6 ("TYA': "++show tyA') $
                vtrace 6 ("xVar: "++show xVar) $                             -- /93@spB^0\\
                vtrace 6 ("xNm: "++show xNm) $
                vtrace 6 ("xVal: "++show xVal) $
                vtrace 6 ("hB: "++show hB) $                
                return $ ( substRecon (l , dist, xNm) recon
                       , reset ctxt 
                         $ deepAppendError (    "CTXT: "++show ctxt 
                                            ++"\nSUBST: "++show l
                                            ++"\nFOR: " ++show (Exi dist xNm tyA)
                                            ++"\nCURRENTLY: " ++show constraint
                                            ++"\nXVAL: "++show xVal
                                            ++"\nDIST: "++show dist
                                           ) 
                         $ subst' (l, Exi dist xNm tyA) $ form 
                       )

        gvar_uvar_outside recon (hA@(dist,_,tyA),ppA) (hB,tyB',mB) = do
          let xVal = len - dist
          onlyIf $ case hB of
            Con _ -> True
            DeBr yVal -> yVal >= xVal
            _ -> False
          
          
          vtrace 4 "*gvar_uvar_outside*" $  return ()
          
          let lppa = length $ viewTyArgs ctxt ppA tyA
          gvar_fixed False recon (xVal , hA, ppA) (liftV (lppa - xVal) hB, tyB', mB) 
          -- "length ppA" because we abstract over all the variables.

        gvar_uvar_inside recon (hA@(dist,_,tyA),ppA) (DeBr yVal,tyB',mB) = do
          let xVal = len - dist
              
          onlyIf $ yVal < xVal
          
          vtrace 4 "*gvar_uvar_inside*" $ return ()
          
          case elemIndex yVal ppA of
            Just hB -> gvar_fixed True recon (xVal, hA, ppA) (DeBr hB, tyB', mB)
            -- not length ppA because we pick one of the variables! 
            Nothing -> lift $ throwTrace 1 $ "GVAR-UVAR-DEPENDS: "++show constraint
                                           ++"\nYVAL: "++show yVal
                                           ++"\nPPA:  "++show ppA
                                           ++"\nCTX:  "++show ctxt
        gvar_uvar_inside _ _ _ = nothing
                  
        raise j v | j <= 0 = v
        raise i (recon, (dist,xNm,tyA), ctx, form) = 
          case upI 1 ctx form of
            Just (ctx'', form) -> 
              let ty = liftV (-1) $ getTy ctx (DeBr 0) -- from the original context! 
                  newExi = (dist - 1, xNm++"@r", forall ty tyA)
                  newpat = Pat $ (liftV 1 $ Var $ uncurriedExi newExi) :+: var 0 

                  substF (Bind ty' f) | ty == ty' = Bind ty' $ subst' (newpat, Exi dist xNm tyA) f
                  substF (a :&: b) = substF a :&: substF b
                  substF r = r

                  frm = substF form
              in  vtrace 8 ("NEW_EXI: "++show newExi) $
                  vtrace 8 ("NEW_PAT: "++show newpat) $
                  vtrace 8 ("TY: "++show ty) $
                  raise (i-1) ( substRecon (newpat, dist, xNm) recon, newExi, ctx'', frm)
            Nothing -> error $ "can't go this high! "++show i 
                          ++ "\nDIST: "++show dist
                          ++ "\nxNm:  "++show xNm
                          ++ "\ntyA:  "++show tyA
                          ++ "\nCTXT: "++show ctx
                          ++ "\nFORM: "++show form
          
        gvar_gvar_diff ((dist,_,_),_) ((dist',xNm',tyA'),_) | dist < dist' = vtrace 4 ("*raise* "++xNm') $  -- THERE IS A BUG HERE!!!!
          case upI (len - dist') ctxt constraint of
            Nothing -> error "constraint shouldn't be done"
            Just (ctxt,form) -> case raise (dist' - dist) (recon , (dist',xNm', liftV (dist' - len) tyA') , ctxt, form) of
              (recon, _,ctxt,form) -> return $ (recon, reset ctxt form)
        gvar_gvar_diff ((dist,_,_),_) ((dist',_,_),_) | dist > dist' = nothing
        gvar_gvar_diff ((dist,xNm,tyA'),ppA) ((_,xNm',tyB'),ppB) = vtrace 4 "*gvar_gvar_diff*" $ do
          let xx'Val = len - dist
              tyA = liftV (-xx'Val) tyA'
              tyB = liftV (-xx'Val) tyB'
          case upI xx'Val ctxt constraint of
            Nothing -> error $ "can't go this high! "++show xx'Val
            Just (ctxt, form) -> do
              let xNm'' = {-"/"++ -} xNm++"+" -- ++xNm'++"\\"

                  sames = [ (var i, var j) | (a,i) <- zip ppA [0..], (b,j) <- zip ppB [0..], a == b ]
                  
                  (samesA,samesB) = unzip sames
                                    
                  getTyLst tb (ty:c) (a:lst) | elem a ppB = forall ty $
                                                         getTyLst tb c lst
                  getTyLst tb (ty:c) (a:lst) = liftV (-1) $ getTyLst tb c lst {- case liftV (-1) $ Abs ty {- should be lazy -} $ Pat $ getTyLst tb c lst of
                    ~(Abs _ (Pat t)) -> t -}
                    
                  getTyLst tb _ _ = tb
                  
                  (tyLstA,tyBaseA) = viewTy ppA tyA -- viewP tyA

              case viewHead tyBaseA of -- always resolve the type before the value!
                Exi{} -> nothing
                _ -> return ()
                
              let (tyLstB,_)       = viewTy ppB tyB  -- viewP tyB
                  
                  tyX' = getTyLst tyBaseA tyLstA ppA
              
                  vlstBaseA = foldl (:+:) (Var $ Exi dist xNm'' $ liftV (length tyLstA) tyX') samesA
                  vlstBaseB = foldl (:+:) (Var $ Exi dist xNm'' $ liftV (length tyLstB) tyX') samesB
                  
                  lA = foldr Abs (Pat vlstBaseA) tyLstA
                  lB = foldr Abs (Pat vlstBaseB) tyLstB
              
              True <- vtrace 6 ("LA:" ++ show lA)
                    $ vtrace 6 ("LB:" ++ show lB)
                    $ vtrace 6 ("TYA:" ++ show tyA)
                    $ vtrace 6 ("TYB:" ++ show tyB)                                            
                    $ vtrace 6 ("PPA:" ++ show ppA)                                            
                    $ vtrace 6 ("CONS:" ++ show constraint)
                    $ return True
              return $ ( substRecon (lA, dist , xNm ) $  
                         substRecon (lB, dist , xNm') $ recon
                       , reset ctxt $ 
                         subst' (lA, Exi dist xNm  tyA) $ 
                         subst' (lB, Exi dist xNm' tyB) $ form
                       )

search :: ( Functor m, Show a, Monad m, Environment a, MonadState Int m) => (a,Form) -> MaybeT m [[(a,Form)]]
search (ctxt,a :&: b) =  search (putLeft ctxt b,a)
                     <|> search (putRight a ctxt,b)
search (ctxt, Bind ty f)    = search (putTy ctxt ty,f)
search (ctxt,Done) = nothing
search (_,_ :=: _)    = nothing
search (_,_ :<: _)    = nothing
search (_,_ :<=: _)   = nothing
search (ctxt,a :@: b) = vtrace 5 "*searchr* " $ (fmap (reset ctxt) <$>) <$> searchR a b
  where searchR search (viewForallP -> Just (a,b)) = do
          yv <- getNewWith "@y"
          let y = evar (height ctxt + 1) yv b
          return $ [[Bind a $ y :=: appN' (liftV 1 search) (var 0) :&: y :@: b]]
        searchR (Pat (tipeView -> Init _)) (tipeView -> Init _) = do
          return [[ a :<: Pat b ]]
        searchR (Pat (tipeView -> UniversalType)) (tipeView -> Init _) = do
          return [[ a :<: Pat b ]]
        searchR (Pat (tipeView -> UniversalType)) (tipeView -> UniversalType) = do
          return [[ a :<: Pat b ]]
        searchR (Pat (tipeView -> Init _)) b = do
          return [[ a :<: Pat b ]] 
        searchR search p = do
          let (constants, anons) = getTypes ctxt
              
              pFam = case viewPat p of
                ~(a,_) -> a
                          
              sameFamily s = case getFamily s of
                Poly -> True
                Family s -> s == pFam
              
              makeFromConstant (c,(Axiom bl i,t)) = if sameFamily t 
                                                    then (\a -> Just ((bl,i),a)) <$> searchL (con c, t) (search,p)
                                                    else return Nothing
              makeFromConstant (c,_) = return Nothing
              
              makeFromAnons (i,t) = if sameFamily t
                                    then (:[]) <$> searchL (var i, t) (search,p)
                                    else return []
              
          let su = do
                cl <- mapM makeFromConstant $ M.toList constants
                rl <- concat <$> mapM makeFromAnons (zip [0..] anons)
                return $ case concatMap isNull $ sortAndUse (catMaybes cl) of
                  [] -> concatMap isNull $ [rl]
                  a:l -> (rl++a):l
          case search of 
            Abs{} -> su
            Pat s -> case viewHead s of
              Exi{} -> su
              h -> do
                rl <- (:[]) <$> searchL (Pat $ Var h, getTy ctxt h) (search,p)
                return $ [ rl ]
              
        searchL (name,attempt) tg@(target,goal) = vtrace 5 ("*searchl* "++show attempt) $ case attempt of
          (viewForallPsimp -> Just (av,b)) -> do
            xv <- getNewWith "@xv"
            let x = evar (height ctxt) xv av
            (:&: x :@: av) <$> searchL (appN ctxt name x, fromType $ appN' b x) tg
          p -> do
            return $ Pat p :=: Pat goal :&: name :=: target
            
isNull [] = []
isNull a = [a]

sortAndUse cl = coalate [] $ sortBy (\a b -> compare (snd $ fst a) (snd $ fst b)) cl
  where coalate [] [] = []
        coalate cg [] = [reverse cg]
        coalate cg (((sequ,_),targ):l) = 
          if sequ -- if sequ is on, then run sequentially
          then if not $ null cg 
               then reverse cg:[targ]:coalate [] l
               else [targ]:coalate [] l
          else coalate (targ:cg) l
                
rebuildC a = (emptyCon $ fst $ getTypes $ fst a, uncurry rebuild a)

-- modify all the time, since the only time we mention an existential 
-- is if we are in the same branch, and we know existentials are unique.
unifyOrSearch recon (cunf, Done) | isDone cunf = return [[(recon, (cunf,Done))]]
unifyOrSearch recon cunf = sunify (Just cunf) <|> tryUnify cunf 
  where -- we perform the search in an ever expanding "outwards" pattern
        -- knowing that local unifications are most likely to effect local
        -- areas.  Although it actually only effects the reconstruction, 
        -- this method prevents any search from being repeated!  
        -- This could practically be made more efficient, but it is theoretically 
        -- efficient enough.  Importantly, this provides some notion of cache coherency
        -- during the search.
        tryUnify (c,Done) | isDone c = return [[(recon, (c,Done))]]
        tryUnify cunf | isDone $ fst cunf = trySearch cunf
        tryUnify cunf =  sunify (viewLeft cunf)
                     <|> sunify (viewRight cunf)
                     <|> tryUnify (nextUp cunf)
                     
                         
        sunify (Just cunf) = (\a -> [[a]]) <$> unify recon cunf
        sunify Nothing = nothing
        
        trySearch cunf = (((\a -> (recon,a)) <$>) <$>) <$> search cunf

interpret :: (Show a, Alternative m, MonadError String m,Environment a, MonadState Int m) =>
             Constants -> (UniContext, (a,Form)) -> m UniContext
interpret _ (recon, (ctxt,Done)) | isDone ctxt = return recon
interpret cons (recon, unf) = vtrace 5 ("\nCONSTRAINTS: "++(show $ uncurry rebuild unf)) $ do
  True <- return $ checkExiForm $ uncurry rebuild unf
  
  m <- runMaybeT $ unifyOrSearch recon unf -- (emptyCon cons :: Ctxt,unf)          
  case m of
    Nothing  -> throwTrace 1 $ "constraints are not satisfiable: "++show unf
    Just lst -> next lst
      where next []     = throwTrace 1 $ "There are no more things to try! "
                          ++"\nCONS: "++show (uncurry rebuild unf)
                          ++"\nLIST: "++show (concatMap (snd <$>) lst)
            next ([]:l) = next l
            next [a] = interpret cons =<< (fail "" <|> F.asum (return <$> a))
            next (a:l)  = appendErr "" current <|> next l -- this will need to be tested extensively
              where current = interpret cons =<< (fail "" <|> F.asum (return <$> a))

unifyAll :: (Alternative m, MonadError String m, MonadState Int m) =>
            ConsGraph -> Constants -> Form -> m UniContext
unifyAll cg cons unf = appendErr "" $ interpret cons ((cg, mempty), (emptyCon cons :: Ctxt, unf))

