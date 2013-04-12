{-# LANGUAGE  
 FlexibleInstances,
 PatternGuards,
 UnicodeSyntax,
 BangPatterns,
 TupleSections,
 ViewPatterns
 #-}
module HOU where

import Choice
import AST
import Substitution
import Context
import TopoSortAxioms
import Control.Monad.State (StateT, forM_,runStateT, modify, get,put, State, runState)
import Control.Monad.RWS (RWST, runRWST, ask, tell, listen)
import Control.Monad.Error (throwError, MonadError)
import Control.Monad (unless, forM, replicateM, void, (<=<), when)
import Control.Monad.Trans (lift)
import Control.Applicative
import qualified Data.Foldable as F
import qualified Data.Traversable as T
import Data.Foldable (foldlM)
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace

import Control.Lens hiding (Choice(..))

import System.IO.Unsafe
import Data.IORef

{-# NOINLINE levelVar #-}
levelVar :: IORef Int
levelVar = unsafePerformIO $ newIORef 0

{-# NOINLINE level #-}
level = unsafePerformIO $ readIORef levelVar

vtrace !i | i < level = trace
vtrace !i = const id

vtraceShow !i1 !i2 s v | i2 < level = trace $ s ++" : "++show v
vtraceShow !i1 !i2 s v | i1 < level = trace s
vtraceShow !i1 !i2 s v = id

throwTrace !i s = vtrace i s $ throwError s

mtrace True = trace
mtrace False = const id


-----------------------------------------------
---  the higher order unification algorithm ---
-----------------------------------------------

flatten :: Constraint -> Env [SCons]
flatten (Bind quant nm ty c) = do
  modifyCtxt $ addToTail "-flatten-" quant nm ty
  flatten c
flatten (c1 :&: c2) = do
  l1 <- flatten c1
  l2 <- flatten c2
  return $ l1 ++ l2
flatten (SCons l) = return l

type UnifyResult = Maybe (Substitution, [SCons], Bool)

unify :: Constraint -> Env Substitution
unify cons =  do
  cons <- vtrace 5 ("CONSTRAINTS1: "++show cons) $ regenAbsVars cons
  cons <- vtrace 5 ("CONSTRAINTS2: "++show cons) $ flatten cons
  let uniWhile :: Substitution -> [SCons] -> Env (Substitution, [SCons])
      uniWhile !sub c' = fail "" <|> do
        exists <- getExists       
        c <- regenAbsVars c'     
        let uniWith !wth backup = searchIn c []
              where searchIn [] r = finish Nothing
                    searchIn (next:l) r = 
                      wth next $ \c1' -> case c1' of
                            Just (sub',next',b) -> finish $ Just (sub', subst sub' (reverse r)++
                                                                        (if b then (++next') else (next'++)) (subst sub' l))
                            Nothing -> searchIn l $ next:r
                    finish Nothing = backup
                    finish (Just (!sub', c')) = do
                      let !sub'' = sub *** sub'
                      modifyCtxt $ subst sub'
                      uniWhile sub'' $! c'
        
        ctxt <- getAllBindings
        
        vtraceShow 2 3 "CONST" c 
          $ vtraceShow 3 3 "CTXT" (reverse ctxt)
          $ uniWith unifyOne 
          $ uniWith unifySearch
          $ uniWith unifySearchAtom
          $ checkFinished c >> return (sub, c)

  sub <- fst <$> uniWhile mempty cons
  
  return $ sub


checkFinished [] = return ()
checkFinished cval = throwTrace 0 $ "ambiguous constraint: " ++show cval

unifySearch :: SCons -> CONT_T b Env UnifyResult
unifySearch (a :@: b) return | b /= tipe = rightSearch a b $ newReturn return
unifySearch _ return = return Nothing

newReturn return cons = return $ case cons of
  Nothing -> Nothing
  Just cons -> Just (mempty, cons, False)

unifySearchAtom :: SCons -> CONT_T b Env UnifyResult
unifySearchAtom (a :@: b) return = rightSearch a b $ newReturn return
unifySearchAtom _ return = return Nothing


unifyOne :: SCons -> CONT_T b Env UnifyResult
unifyOne (a :=: b) return = do
  c' <- isolateForFail $ unifyEq $ a :=: b 
  case c' of 
    Nothing -> return =<< (isolateForFail $ unifyEq $ b :=: a)
    r -> return r
unifyOne _ return = return Nothing

impForallPrefix (Spine "#imp_forall#" [ty, Abs nm _ l]) = nm:impForallPrefix l
impForallPrefix _ = []

impAbsPrefix (Spine "#imp_abs#" (ty:(Abs nm _ l):r)) = nm:impAbsPrefix l
impAbsPrefix _ = []

unifyEq cons@(a :=: b) = case (a,b) of 
  
  (Spine "#ascribe#" (ty:v:l), b) -> return $ Just (mempty, [rebuildSpine v l :=: b], False)
  (b,Spine "#ascribe#" (ty:v:l)) -> return $ Just (mempty, [b :=: rebuildSpine v l], False)
  
  (Spine "#imp_forall#" [ty, Abs nm _ l], Spine "#imp_forall#" [ty',Abs nm' _ l']) | nm == nm' -> do
    a <- getNewWith "@aL"
    modifyCtxt $ addToTail "-implicit-" Forall a ty
    return $ Just (mempty, [Abs nm ty l `apply` var a :=: Abs nm' ty' l' `apply` var a , ty :=: ty'], False)

  -- this case doesn't cover the case where we have 
  -- ?\/x : t . A  =:= ?\/x :t . A, but "x in t" isn't necessarily solvable.
    
  -- this is solvable if we defer instantiation of x if we see x in b.
  -- by these rules though, ?\/x y : t1 . A =:= ?\/ y x : t1 . A  is not provable.
  -- this appears to be fine for the moment, although it won't imediately be derivable from the implicit CoC  
  -- where such a statement is true.  
  (Spine "#imp_forall#" [ty, l@(Abs nm _ _)], b) | not $ elem nm $ impForallPrefix b -> vtrace 1 "-implicit-" $ do
    a' <- getNewWith "@aL"
    modifyCtxt $ addToTail "-implicit-" Exists a' ty
    return $ Just (mempty, [l `apply` var a' :=: b , var a' :@: ty], False)
    
  (b, Spine "#imp_forall#" [ty, l@(Abs nm _ _)]) | not $ elem nm $ impForallPrefix b -> vtrace 1 "-implicit-" $ do
    a' <- getNewWith "@aR"
    modifyCtxt $ addToTail "-implicit-" Exists a' ty
    return $ Just (mempty,  [b :=: l `apply` var a' , var a' :@: ty], False)
    
  (Spine "#imp_abs#" (ty:(Abs nm _ l):r), Spine "#imp_abs#" (ty':(Abs nm' _ l'):r')) | nm == nm' -> do
    a <- getNewWith "@aL"
    modifyCtxt $ addToTail "-implicit-" Forall a ty
    return $ Just (mempty, [rebuildSpine (Abs nm ty l) (var a:r) :=: rebuildSpine (Abs nm' ty' l') (var a:r'), ty :=: ty'], False)
    
  (Spine "#imp_abs#" (ty:(l@(Abs nm _ _)):r), b) | not $ elem nm $ impAbsPrefix b -> vtrace 1 ("-imp_abs- : "++show a ++ "\n\t"++show b) $ do
    a <- getNewWith "@iaL"
    modifyCtxt $ addToTail "-imp_abs-" Exists a ty
    return $ Just (mempty, [rebuildSpine l (var a:r) :=: b , var a :@: ty], False)
  (b, Spine "#imp_abs#" (ty:(l@(Abs nm _ _)):r)) | not $ elem nm $ impAbsPrefix b -> vtrace 1 "-imp_abs-" $ do
    a <- getNewWith "@iaR"
    modifyCtxt $ addToTail "-imp_abs-" Exists a ty
    return $ Just (mempty, [b :=: rebuildSpine l (var a:r) , var a :@: ty], False)

  (Spine "#tycon#" [Spine nm [_]], Spine "#tycon#" [Spine nm' [_]]) | nm /= nm' -> throwTrace 0 $ "different type constraints: "++show cons
  (Spine "#tycon#" [Spine nm [val]], Spine "#tycon#" [Spine nm' [val']]) | nm == nm' -> 
    return $ Just (mempty, [val :=: val'], False)

  (Abs nm ty s , Abs nm' ty' s') -> vtrace 1 "-aa-" $ do
    modifyCtxt $ addToTail "-aa-" Forall nm ty
    return $ Just (mempty, [ty :=: ty' , s :=: subst (nm' |-> var nm) s'], False)
  (Abs nm ty s , s') -> vtraceShow 1 2 "-asL-" cons $ do
    modifyCtxt $ addToTail "-asL-" Forall nm ty
    return $ Just (mempty, [s :=: s' `apply` var nm], False)

  (s, Abs nm ty s' ) -> vtraceShow 1 2 "-asR-" cons $ do
    modifyCtxt $ addToTail "-asR-" Forall nm ty
    return $ Just (mempty, [s `apply` var nm :=: s'], False)

  (s , s') | s == s' -> vtrace 1 "-eq-" $ return $ Just (mempty, [], False)
  (s@(Spine x yl), s') -> vtraceShow 4 5 "-ss-" cons $ do
    bind <- getElm ("all: "++show cons) x
    case bind of
      Left bind@Binding{ elmQuant = Exists, elmType = ty } -> vtraceShow 4 5 "-g?-" cons $ do
        fors <- getForallsAfter bind
        exis <- getExistsAfter bind
        case s' of
            b@(Spine x' y'l) -> vtraceShow 4 5 "-gs-" cons $ do
              bind' <- getElm ("gvar-blah: "++show cons) x' 
              case bind' of
                Right ty' -> vtraceShow 1 2 "-gc-" cons $ -- gvar-const
                  if allElementsAreVariablesNoPP fors yl
                  then gvar_const (Spine x yl, ty) (Spine x' y'l, ty')  
                  else return Nothing
                Left Binding{ elmQuant = Forall } | (not $ elem (var x') yl) && S.member x' fors -> 
                  if allElementsAreVariables fors yl 
                  then throwTrace 0 $ "CANT: gvar-uvar-depends: "++show (a :=: b)
                  else return Nothing
                Left Binding{ elmQuant = Forall } | S.member x $ freeVariables y'l -> 
                  if allElementsAreVariables fors yl 
                  then throwTrace 0 $ "CANT: occurs check: "++show (a :=: b)
                  else return Nothing
                Left Binding{ elmQuant = Forall, elmType = ty' } | S.member x' fors -> vtraceShow 1 5 "-gui-" cons $  -- gvar-uvar-inside
                  if allElementsAreVariables fors yl
                  then gvar_uvar_inside (Spine x yl, ty) (Spine x' y'l, ty')
                  else return Nothing
                Left Binding{ elmQuant = Forall, elmType = ty' } -> vtraceShow 1 5 "-guo-" cons $ 
                  if allElementsAreVariablesNoPP fors yl
                  then gvar_uvar_outside (Spine x yl, ty) (Spine x' y'l, ty')
                  else return Nothing
                Left bind'@Binding{ elmQuant = Exists, elmType = ty'} -> vtraceShow 4 5 "-gg-" cons $
                  if not $ allElementsAreVariables fors yl && allElementsAreVariables fors y'l && S.member x' exis
                  then return Nothing 
                  else if x == x' 
                       then vtraceShow 1 2 "-ggs-" cons $ -- gvar-gvar-same
                         gvar_gvar_same (Spine x yl, ty) (Spine x' y'l, ty')
                       else -- gvar-gvar-diff
                         if S.member x $ freeVariables y'l 
                         then throwTrace 0 $ "CANT: ggd-occurs check: "++show (a :=: b)
                         else vtraceShow 1 2 "-ggd-" cons $ gvar_gvar_diff bind (Spine x yl, ty) (Spine x' y'l, ty') bind'
            _ -> vtraceShow 1 5 "-ggs-" cons $ return Nothing
      _ -> vtrace 4 "-u?-" $ case s' of 
        b@(Spine x' _) | x /= x' -> do
          bind' <- getElm ("const case: "++show cons) x'
          case bind' of
            Left Binding{ elmQuant = Exists } -> return Nothing
            _ -> throwTrace 0 ("CANT: -uud- two different universal equalities: "++show (a :=: b)) -- uvar-uvar 

        Spine x' yl' | x == x' -> vtraceShow 1 2 "-uue-" (a :=: b) $ do -- uvar-uvar-eq
          
          let match ((Spine "#tycon#" [Spine nm [a]]):al) bl = case findTyconInPrefix nm bl of
                Nothing -> match al bl
                Just (b,bl) -> ((a :=: b) :) <$> match al bl
          -- in this case we know that al has no #tycon#s in its prefix since we exhausted all of them in the previous case
              match al (Spine "#tycon#" [Spine _ [_]]:bl) = match al bl 
              match (a:al) (b:bl) = ((a :=: b) :) <$> match al bl 
              match [] [] = return []
              match _ _ = throwTrace 0 $ "CANT: different numbers of arguments: "++show cons

          cons <- match yl yl'
          return $ Just (mempty, cons, False)
        _ -> throwTrace 0 $ "CANT: uvar against a pi WITH CONS "++show cons
            
allElementsAreVariables :: S.Set Name -> [Spine] -> Bool
allElementsAreVariables fors = partialPerm mempty 
  where partialPerm s [] = True
        partialPerm s (Spine nm []:l) | S.member nm fors && not (S.member nm s) = 
          partialPerm (S.insert nm s) l
        partialPerm _ _ = False
        
allElementsAreVariablesNoPP fors = partial
  where partial [] = True
        partial (Spine nm []:l) | S.member nm fors = partial l
        partial _ = False
        

typeToListOfTypes (Spine "#forall#" [_, Abs x ty l]) = (x,ty):typeToListOfTypes l
typeToListOfTypes (Spine _ _) = []
typeToListOfTypes a@(Abs _ _ _) = error $ "not a type" ++ show a

-- the problem WAS (hopefully) here that the binds were getting
-- a different number of substitutions than the constraints were.
-- make sure to check that this is right in the future.
raiseToTop top@Binding{ elmNext = Just k}  bind@Binding{ elmName = x, elmType = ty } sp m | k == x = 
  m (sp, ty) mempty
raiseToTop top bind@Binding{ elmName = x, elmType = ty } sp m = do
  hl <- reverse <$> getBindingsBetween top bind
  x' <- getNewWith "@newx"
  
  let newx_args = map (var . fst) hl
      sub = x |-> Spine x' newx_args
      
      ty' = foldr (\(nm,ty) a -> forall nm ty a) ty hl
        
      addSub Nothing = return Nothing
      addSub (Just (sub',cons,b)) = do
        -- we need to solve subst twice because we might reify twice
        let sub'' = ((subst sub' <$> sub) *** sub') 

        modifyCtxt $ subst sub'
        return $ Just (sub'', cons,b)
        
  modifyCtxt $ addAfter "-rtt-" (elmName top) Exists x' ty' . removeFromContext x
  vtrace 3 ("RAISING: "++x' ++" +@+ "++ show newx_args ++ " ::: "++show ty'
         ++"\nFROM: "++x ++" ::: "++ show ty
          ) modifyCtxt $ subst sub
  
  -- now we can match against the right hand side
  r <- addSub =<< m (subst sub sp, ty') sub
  modifyCtxt $ removeFromContext x'
  return r

      
getBase 0 a = a
getBase n (Spine "#forall#" [_, Abs _ _ r]) = getBase (n - 1) r
getBase _ a = a

makeBind xN us tyl arg = foldr (uncurry Abs) (Spine xN $ map var arg) $ zip us tyl

gvar_gvar_same (a@(Spine x yl), aty) (b@(Spine _ y'l), _) = do
  aty <- regenAbsVars aty
  let n = length yl
         
      (uNl,atyl) = unzip $ take n $ typeToListOfTypes aty
      
  xN <- getNewWith "@ggs"
  
  let perm = [iyt | (iyt,_) <- filter (\(_,(a,b)) -> a == b) $ zip (zip uNl atyl) (zip yl y'l) ]
      
      l = makeBind xN uNl atyl $ map fst perm
      
      xNty = foldr (uncurry forall) (getBase n aty) perm
      
      sub = x |-> l
      
  modifyCtxt $ addBefore "-ggs-" x Exists xN xNty -- THIS IS DIFFERENT FROM THE PAPER!!!!
  modifyCtxt $ removeFromContext x
  
  return $ Just (sub, [], False) -- var xN :@: xNty])
  
gvar_gvar_same _ _ = error "gvar-gvar-same is not made for this case"

gvar_gvar_diff top (a',aty') (sp, _) bind = raiseToTop top bind sp $ \b subO -> do
  let a = (subst subO a', subst subO aty')
  gvar_gvar_diff' a b
  
gvar_gvar_diff'  (Spine x yl, aty) ((Spine x' y'l), bty) = do
      -- now x' comes before x 
      -- but we no longer care since I tested it, and switching them twice reduces to original
  let n = length yl
      m = length y'l
      
  aty <- regenAbsVars aty
  bty <- regenAbsVars bty
  
  let (uNl,atyl) = unzip $ take n $ typeToListOfTypes aty
      (vNl,btyl) = unzip $ take m $ typeToListOfTypes bty
      
  xN <- getNewWith "@ggd"
  
  let perm = do
        (iyt,y) <- zip (zip uNl atyl) yl
        (i',_) <- filter (\(_,y') -> y == y') $ zip vNl y'l 
        return (iyt,i')
      
      l = makeBind xN uNl atyl $ map (fst . fst) perm
      l' = makeBind xN vNl btyl $ map snd perm
      
      xNty = foldr (uncurry forall) (getBase n aty) (map fst perm)
      
      sub = (x' |-> l') *** (x |-> l) -- M.fromList [(x , l), (x',l')]

  modifyCtxt $ addBefore "-ggd-" x Exists xN xNty -- THIS IS DIFFERENT FROM THE PAPER!!!!
  modifyCtxt $ subst sub . removeFromContext x . removeFromContext x'
  vtrace 3 ("SUBST: -ggd- "++show sub) $ 
    return $ Just (sub, [] {- var xN :@: xNty] -}, False)
  
gvar_uvar_inside a@(Spine _ yl, _) b@(Spine y _, _) = 
  case elemIndex (var y) $ reverse yl of
    Nothing -> return Nothing
    Just _ -> gvar_uvar_possibilities a b
gvar_uvar_inside _ _ = error "gvar-uvar-inside is not made for this case"

gvar_uvar_outside = gvar_const

gvar_const a@(s@(Spine x yl), _) b@(s'@(Spine y _), bty) = gvar_fixed a b $ var . const y
gvar_const _ _ = error "gvar-const is not made for this case"

gvar_uvar_possibilities a@(s@(Spine x yl),_) b@(s'@(Spine y _),bty) = 
  case elemIndex (var y) yl of
    Just i -> gvar_fixed a b $ (!! i)
    Nothing -> throwTrace 0 $ "CANT: gvar-uvar-depends: "++show (s :=: s')
gvar_uvar_possibilities _ _ = error "gvar-uvar-possibilities is not made for this case"

getTyNews (Spine "#forall#" [_, Abs _ _ t]) = Nothing:getTyNews t
getTyNews (Spine "#imp_forall#" [_, Abs nm _ t]) = Just nm:getTyNews t
getTyNews _ = []

gvar_fixed (a@(Spine x _), aty) (b@(Spine _ y'l), bty) action = do
  let m = getTyNews bty
      cons = a :=: b
  
  let getArgs (Spine "#forall#" [ty, Abs ui _ r]) = ((var ui,ui),Left ty):getArgs r
      getArgs (Spine "#imp_forall#" [ty, Abs ui _ r]) = ((tycon ui $ var ui,ui),Right ty):getArgs r
      getArgs _ = []
      
      untylr = getArgs aty
      (un,_) = unzip untylr 
      (vun, _) = unzip un
  
  xm <- forM m $ \j -> do
    x <- getNewWith "@xm"
    return (x, (Spine x vun, case j of
      Nothing -> Spine x vun
      Just a -> tycon a $ Spine x vun))  
      
  let xml = map (snd . snd) xm
      -- when rebuilding the spine we want to use typeconstructed variables if bty contains implicit quantifiers
      toLterm (Spine "#forall#" [ty, Abs ui _ r]) = Abs ui ty $ toLterm r
      toLterm (Spine "#imp_forall#" [ty, Abs ui _ r]) = imp_abs ui ty $ toLterm r      
      toLterm _ = rebuildSpine (action vun) $ xml

      
      l = toLterm aty
  
      vbuild e = foldr (\((_,nm),ty) a -> case ty of
                           Left ty -> forall nm ty a
                           Right ty -> imp_forall nm ty a
                       ) e untylr
                 
      -- returns the list in the same order as xm
      substBty sub (Spine "#forall#" [_, Abs vi bi r]) ((x,xi):xmr) = (x,vbuild $ subst sub bi)
                                                                :substBty (M.insert vi (fst xi) sub) r xmr
      substBty sub (Spine "#imp_forall#" [_, Abs vi bi r]) ((x,xi):xmr) = (x,vbuild $ subst sub bi)
                                                                    : substBty (M.insert vi (fst xi) sub) r xmr
      substBty _ _ [] = []
      substBty _ s l  = error $ "is not well typed: "++show s
                        ++"\nFOR "++show l 
                        ++ "\nON "++ show cons
      
      sub = x |-> l -- THIS IS THAT STRANGE BUG WHERE WE CAN'T use x in the output substitution!
      addExists s t = vtrace 3 ("adding: "++show s++" ::: "++show t) $ addAfter "-gf-" x Exists s t
      -- foldr ($) addBeforeX [x1...xN]
  modifyCtxt $ flip (foldr ($)) $ uncurry addExists <$> substBty mempty bty xm 
  modifyCtxt $ subst sub . removeFromContext x
  vtrace 4 ("RES: -gg- "++(show $ subst sub $ a :=: b)) $ 
    vtrace 4 ("FROM: -gg- "++(show $ a :=: b)) $ 
    return $ Just (sub, [ subst sub $ a :=: b -- this ensures that the function resolves to the intended output
                        ], False)

gvar_fixed _ _ _ = error "gvar-fixed is not made for this case"

--------------------
--- proof search ---  
--------------------


-- need bidirectional search!
rightSearch :: Term -> Type -> CONT_T b Env (Maybe [SCons])
rightSearch m goal ret = vtrace 1 ("-rs- "++show m++" ∈ "++show goal) $ fail (show m++" ∈ "++show goal) <|>
  case goal of
    Spine "#forall#" [a, b] -> do
      y <- getNewWith "@sY"
      x' <- getNewWith "@sX"
      let b' = b `apply` var x'
      modifyCtxt $ addToTail "-rsFf-" Forall x' a
      modifyCtxt $ addToTail "-rsFe-" Exists y b'
      ret $ Just [ var y :=: m `apply` var x' , var y :@: b']

    Spine "#imp_forall#" [_, Abs x a b] -> do
      y <- getNewWith "@isY"
      x' <- getNewWith "@isX"
      let b' = subst (x |-> var x') b
      modifyCtxt $ addToTail "-rsIf-" Forall x' a        
      modifyCtxt $ addToTail "-rsIe-" Exists y b'
      ret $ Just [ var y :=: m `apply` (tycon x $ var x')
                 , var y :@: b'
                 ]
    Spine "putChar" [c@(Spine ['\'',l,'\''] [])] -> ret $ Just $ (m :=: Spine "putCharImp" [c]):seq action []
      where action = unsafePerformIO $ putStr $ l:[]

    Spine "putChar" [_] -> vtrace 0 "FAILING PUTCHAR" $ ret Nothing
  
    Spine "readLine" [l] -> 
      case toNCCstring $ unsafePerformIO $ getLine of
        s -> do -- ensure this is lazy so we don't check for equality unless we have to.
          y <- getNewWith "@isY"
          let ls = l `apply` s
          modifyCtxt $ addToTail "-rl-" Exists y ls
          ret $ Just [m :=: Spine "readLineImp" [l,s {- this is only safe because lists are lazy -}, var y], var y :@: Spine "run" [ls]]

    Spine nm _ -> do
      constants <- getConstants
      foralls <- getForalls
      exists <- getExists
      let env = M.union foralls constants
          
          isBound a = M.member a exists || M.member a env
          isFixed a = isChar a || M.member a env
      
          getFixedType a | isChar a = Just $ anonymous $ var "char"
          getFixedType a = M.lookup a env
      
      let mfam = case m of 
            Abs{} -> Nothing
            Spine nm _ -> case getFixedType nm of
              Just t -> Just (nm,t)
              Nothing -> Nothing

          sameFamily (_, (_,Abs{})) = False
          sameFamily ("pack",_) = "exists" == nm -- if we are searching for exists, try to pack!
          sameFamily (_,(_,s)) = ( getFamily s == nm ) && 
                                 all isBound (S.toList $ freeVariables s)
          
      targets <- case mfam of
        Just (nm,t) -> return $ [(nm,t)]
        Nothing -> do
          return $ filter sameFamily $ M.toList constants ++ M.toList foralls
          
      if all isFixed $ S.toList $ S.union (freeVariables m) (freeVariables goal)
        then ret $ Just []
        else case targets of
          [] -> ret Nothing
          _  -> inter [] $ sortBy (\a b -> compare (getVal a) (getVal b)) targets
            where ls (nm,target) = leftSearch (m,goal) (var nm, target)
                  getVal = snd . fst . snd
                  
                  inter [] [] = throwError "no more options"
                  inter cg [] = F.asum $ reverse cg
                  inter cg ((nm,((sequ,_),targ)):l) = do
                    res <- Just <$> ls (nm,targ)
                    if sequ 
                      then (if not $ null cg then (appendErr "" (F.asum $ reverse cg) <|>) else id) $ 
                           (appendErr "" $ ret res) <|> inter [] l
                      else inter (ret res:cg) l
                      
                      
a .-. s = foldr (\k v -> M.delete k v) a s 

leftSearch (m,goal) (x,target) = vtrace 1 ("LS: " ++ show x++" ∈ " ++show target++" >> " ++show m ++" ∈ "++ show goal)
                               $ leftCont x target
  where leftCont n target = case target of
          Spine "#forall#" [a, b] -> do
            x' <- getNewWith "@sla"
            modifyCtxt $ addToTail "-lsF-" Exists x' a
            cons <- leftCont (n `apply` var x') (b `apply` var x')
            return $ cons++[var x' :@: a]

          Spine "#imp_forall#" [_ , Abs x a b] -> do  
            x' <- getNewWith "@isla"
            modifyCtxt $ addToTail "-lsI-" Exists x' a
            cons <- leftCont (n `apply` (tycon x $ var x')) (subst (x |-> var x') b)
            return $ cons++[var x' :@: a]
          Spine _ _ -> do
            return $ [goal :=: target, m :=: n]
          _ -> error $ "λ does not have type atom: " ++ show target


search :: Type -> Env (Substitution, Term)
search ty = do
  e <- getNewWith "@e"
  sub <- unify $ (∃) e ty $ SCons [var e :@: ty]
  return $ (sub, subst sub $ var e)


----------------------------
---  Universe Checking   ---
----------------------------
  
viewLast (reverse -> (a:l)) = (reverse l,a)

viewApp (Spine nm (viewLast -> (l,arg))) = (Spine nm l, arg)

lessThan (Spine a [Spine nm []]) (Spine b [Spine nm' []]) | a == tipeName && b == tipeName = tell [(nm,nm')]
lessThan a b = throwTrace 0 $ "Expecting type: "++show a ++ "  <  "++show b

universeCheck nm env sp = case sp of
  Abs nm ty a -> do
    universeCheck nm env ty
    let env' = M.insert nm ty env
    tyR <- universeCheck nm env' a
    universeCheck nm env' tyR
    return $ forall nm ty tyR
    
  Spine "#imp_abs#" [_, Abs nm ty a] -> do
    universeCheck nm env ty
    let env' = M.insert nm ty env
    tyR <- universeCheck nm env' a
    universeCheck nm env' tyR
    return $ imp_forall nm ty tyR    
      
  Spine "#forall#" [_, Abs nm ty l] -> do  
    k1 <- universeCheck nm env ty
    k2 <- universeCheck nm (M.insert nm ty env) l
    k3 <- (tipe `apply`) <$> var <$> getNewWith "@tv"
    
    lessThan k1 k3
    lessThan k2 k3
    return k3
  Spine "#ascribe#" [ty,a] -> do
    universeCheck nm env ty
    --universeCheck nm env a
    return ty
  Spine "#imp_forall#" [_, Abs nm ty l] -> do  
    k1 <- universeCheck nm env ty
    k2 <- universeCheck nm (M.insert nm ty env) l

    k3 <- (tipe `apply`) <$> var <$> getNewWith "@tv"
    lessThan k1 k3
    lessThan k2 k3
    return k3
    
  Spine a [Spine v []] | a == tipeName -> do 
    v' <- getNewWith "@tipeLevelRetB"
    tell [(v,v')]
    return $ tipe `apply` var v'
    
  Spine "#tycon#" [Spine nm [l]] -> universeCheck nm env l
  Spine ['\'',c,'\''] [] -> return $ var "char"
  Spine nm [] -> case env ! nm of
    Nothing -> throwError $ "not in the enviroment: "++show nm
    Just a  -> return a

  (viewApp -> (f,a)) -> do
    (fty,lst1) <- listen $ universeCheck nm env f
    (aty,lst2) <- listen $ universeCheck nm env a
    let lsts = lst1 ++ lst2
    tell lsts    
    checkU nm lsts -- LOCAL UNIVERSE CHECKING - socool!!!! 

    let byob fty = case fty of
          Spine "#imp_forall#" [ty, v] -> (Spine "#imp_abs#" [ty,v]) `apply` a
          Spine "#forall#" [ty, v] -> v `apply` a
          -- Do some local universe checking!
          Spine "#ascribe#" (t:v:l) ->  byob $ rebuildSpine v l
          
    return $ byob fty 

initTypes (Spine a []) | a == tipeName = do
  v <- getNewWith "@tipeLevel"
  return $ Spine a [var v]
initTypes (Spine nm l) = Spine nm <$> T.mapM initTypes l
initTypes (Abs nm ty a) = do
  ty <- initTypes ty
  Abs nm ty <$> initTypes a
  
checkU nm lst = do
  let graph = foldr (\(nm,lt) gr -> case gr ! nm of 
                        Nothing -> M.insert nm (S.singleton lt) gr
                        Just r -> M.insert nm (S.insert lt r)   gr) mempty lst
      
  if isUniverseGraph graph 
    then return ()
    else throwError $ "Impredicative use of type in: "++nm

checkUniverses :: String -> M.Map Name Type -> Type -> Choice ()
checkUniverses nm env ty = do
  (_,_,lst) <- (\a -> runRWST a () emptyState) $ do
    env <- T.mapM initTypes $ M.union constsMap env
    ty <- initTypes ty
    universeCheck nm env ty
  checkU nm lst
-----------------------------
--- constraint generation ---
-----------------------------

(≐) a b = lift $ tell $ SCons [a :=: b]
(.@.) a b = lift $ tell $ SCons [a :@: b]

      
      
withKind m = m tipe

checkType :: Bool -> Spine -> Type -> TypeChecker Spine
checkType b sp ty = case sp of
  Spine "#hole#" [] -> do
    x' <- getNewWith "@hole"
    
    addToEnv (∃) x' ty $ do
      var x' .@. ty
      return $ var x'
  
  Spine "#ascribe#" (t:v:l) -> do
    (v'',mem) <- regenWithMem v
    t   <- withKind $ checkType b t
    t'' <- regenAbsVars t
    v'  <- checkType b v'' t
    r   <- getNewWith "@r"
    Spine _ l' <- addToEnv (∀) r t'' $ checkType b (Spine r l) ty
    
    if b 
      then return $ rebuildSpine (rebuildFromMem mem v') l'
      else return $ rebuildSpine (ascribe (rebuildFromMem mem v') t) l'
    
  Spine "#infer#" [_, Abs x tyA tyB ] -> do
    tyA <- withKind $ checkType b tyA
    x' <- getNewWith "@inf"
    addToEnv (∃) x' tyA $ do
      var x' .@. tyA
      checkType b (subst (x |-> var x') tyB) ty

  Spine "#dontcheck#" [v] -> do
    return v
           
  Spine "#imp_forall#" [_, Abs x tyA tyB] -> do
    tyA <- withKind $ checkType b tyA
    tyB <- addToEnv (∀) x tyA $ checkType b tyB ty
    return $ imp_forall x tyA tyB
    
  Spine "#forall#" [_, Abs x tyA tyB] -> do
    tyA <- withKind $ checkType b tyA
    forall x tyA <$> (addToEnv (∀) x tyA $ 
      checkType b tyB ty )

  -- below are the only cases where bidirectional type checking is useful 
  Spine "#imp_abs#" [_, Abs x tyA sp] -> case ty of
    Spine "#imp_forall#" [_, Abs x' tyA' tyF'] | x == x' || "" == x' -> do
      tyA <- withKind $ checkType b tyA
      tyA ≐ tyA'
      addToEnv (∀) x tyA $ do
        imp_abs x tyA <$> checkType b sp tyF'
    _ -> do
      -- here this acts like "infers" since we can always initialize a ?\ like an infers!
      tyA <- withKind $ checkType b tyA
      x' <- getNewWith "@inf"
      addToEnv (∃) x' tyA $ do
        var x' .@. tyA
        checkType b (subst (x |-> var x') sp) ty 
{-
    _ -> do
      e <- getNewWith "@e"
      tyA <- withKind $ checkType b tyA
      withKind $ \k -> addToEnv (∃) e (forall x tyA k) $ do
        imp_forall x tyA (Spine e [var x]) ≐ ty
        sp <- addToEnv (∀) (check "impabs2" x) tyA $ 
          checkType b sp (Spine e [var x])
        return $ imp_abs x tyA sp
-}
  Abs x tyA sp -> case ty of
    Spine "#forall#" [_, Abs x' tyA' tyF'] -> do
      tyA <- withKind $ checkType b tyA
      tyA ≐ tyA'
      addToEnv (∀) x tyA $ do
        Abs x tyA <$> checkType b sp (subst (x' |-> var x) tyF')
    _ -> do
      e <- getNewWith "@e"
      tyA <- withKind $ checkType b tyA
      withKind $ \k -> addToEnv (∃) e (forall "" tyA k) $ do
        forall x tyA (Spine e [var x]) ≐ ty
        Abs x tyA <$> (addToEnv (∀) x tyA $ checkType b sp (Spine e [var x]))
  Spine nm [] | isChar nm -> do
    ty ≐ Spine "char" []
    return sp
  Spine head args -> do
    let chop mty [] = do
          ty ≐ mty
          return []
          
        chop mty lst@(a:l) = case mty of 
          
          Spine "#imp_forall#" [ty', Abs nm _ tyv] -> case findTyconInPrefix nm lst of
            Nothing -> do
              x <- getNewWith "@xin"
              addToEnv (∃) x ty' $ do
                var x .@. ty' 
                -- we need to make sure that the type is satisfiable such that we can reapply it!
                (tycon nm (var x):) <$> chop (subst (nm |-> var x) tyv) lst

            Just (val,l) -> do
              val <- checkType b val ty'
              (tycon nm val:) <$> chop (subst (nm |-> val) tyv) l
          Spine "#forall#" [ty', c] -> do
            a <- checkType b a ty'
            (a:) <$> chop (c `apply` a) l
          _ -> withKind $ \k -> do  
            x <- getNewWith "@xin"
            z <- getNewWith "@zin"
            tybody <- getNewWith "@v"
            let tybodyty = forall z (var x) k
            withKind $ \k' -> addToEnv (∃) x k' $ addToEnv (∃) tybody tybodyty $ do 
              a <- checkType b a (var x)
              v <- getNewWith "@v"
              forall v (var x) (Spine tybody [var v]) ≐ mty
              (a:) <$> chop (Spine tybody [a]) l

    mty <- (! head) <$> lift getFullCtxt
    
    case mty of 
      Nothing -> lift $ throwTrace 0 $ "variable: "++show head++" not found in the environment."
                                     ++ "\n\t from "++ show sp
                                     ++ "\n\t from "++ show ty
      Just ty' -> Spine head <$> chop (snd ty') args

checkFullType :: Bool -> Spine -> Type -> Env (Spine, Constraint)
checkFullType b val ty = typeCheckToEnv $ checkType b val ty


---------------------------------
--- Generalize Free Variables ---
---------------------------------
type Graph k = M.Map k (S.Set k)
        
isGen [] = False
isGen (c:s) = elem c ['A'..'Z']
getGenTys sp = S.filter isGen $ freeVariables sp

{- 
Employ the use order heuristic, where 
variables are ordered by use on the same level in terms.
-}
buildOrderGraph :: S.Set Name -- the list of variables to be generalized
                -> S.Set Name -- the list of previously seen variables
                -> Spine 
                -> State (Graph Name) -- an edge in the graph if a variable has occured before this one.
                         (S.Set Name) -- the generalizable variables that occured in said term.
buildOrderGraph gen prev s = case s of
  Abs nm t v -> do
    prev1 <- buildOrderGraph gen prev t
    prev2 <- buildOrderGraph (S.delete nm gen) prev v
    return $ S.union prev1 prev2
  Spine s [t, l] | elem s [ "#imp_abs#"] -> do
    prev1 <- buildOrderGraph gen prev t
    prev2 <- buildOrderGraph gen prev l
    return $ S.union prev1 prev2    
  Spine "#tycon#" [Spine _ [l]] -> buildOrderGraph gen prev l  

  Spine nm l -> do
    mp <- get
    prev' <- if S.member nm gen
             then do
               let prevs = mp M.! nm
               put $ M.insert nm (S.union prev prevs) mp
               return $ mempty
             else return prev
      
    prev'' <- foldlM (buildOrderGraph gen) prev' l

    if S.member nm gen
      then do
      mp <- get
      let prevs = mp M.! nm
      put $ M.insert nm (S.union prev'' prevs) mp
      return $ S.singleton nm
      else return mempty

        
generateBinding sp = foldr (\a b -> imp_forall a ty_hole b) sp orderedgens
  where genset = getGenTys sp
        genlst = S.toList genset
        (_,graph) = runState (buildOrderGraph genset mempty sp) (M.fromList $ map (,mempty) genlst)
        orderedgens = vtrace 0 ("ARG_GRAPH: "++show graph) $ topoSortComp (\a -> (a, graph M.! a)) genlst

----------------------
--- type inference ---
----------------------
typeInfer :: Bool -> ContextMap -> ((Bool,Integer),Name,Term,Type) -> Choice (Term, Type, ContextMap)
typeInfer b env (seqi,nm,val,ty) = (\r -> (\(a,_,_) -> a) <$> runRWST r (M.union envConsts env) emptyState) $ do
  ty <- return $ alphaConvert mempty mempty ty
  val <- return $ alphaConvert mempty mempty val
  
  (ty,mem') <- regenWithMem ty
  (val,mem) <- vtrace 1 ("ALPHAD TO: "++show val) $ regenWithMem val
  
  (val,constraint) <- vtrace 1 ("REGENED TO: "++show val) $ checkFullType b val ty
  
  sub <- appendErr ("which became: "++show val ++ "\n\t :  " ++ show ty) $ 
         unify constraint
  
  let resV = rebuildFromMem mem  $ unsafeSubst sub $ eta_expandAll (snd <$> env) val
      resT = rebuildFromMem mem' $ unsafeSubst sub $ eta_expandAll (snd <$> env) ty

  vtrace 0 ("result: "++show resV) $
      return $ (resV,resT, M.insert nm (seqi,resV) env)

unsafeSubst s (Spine nm apps) = let apps' = unsafeSubst s <$> apps in case s ! nm of 
  Just nm -> rebuildSpine nm apps'
  _ -> Spine nm apps'
unsafeSubst s (Abs nm tp rst) = Abs nm (unsafeSubst s tp) (unsafeSubst s rst)
  

----------------------------
--- the public interface ---
----------------------------

typePipe verbose lt (b,nm,ty,kind) = do
  (ty,kind,lt) <- mtrace verbose ("Inferring:   " ++nm) $ 
                  typeInfer False lt (b,nm, ty,kind) -- type infer
                  
  checkUniverses nm (snd <$> lt) (ascribe ty kind)

  (ty,kind,lt) <- mtrace verbose ("Elaborating: " ++nm) $ 
                  typeInfer True lt (b,nm, ty,kind) -- elaborate                  
                  
  (ty,kind,lt) <- mtrace verbose ("Checking:    " ++nm) $ 
                  typeInfer True lt (b,nm, ty,kind) -- type check
                  

  
  return (ty,kind,lt)
  
typeCheckAxioms :: Bool -> [FlatPred] -> Choice (Substitution, Substitution)
typeCheckAxioms verbose lst = do
  
  -- check the closedness of families.  this gets done
  -- after typechecking since family checking needs to evaluate a little bit
  -- in order to allow defs in patterns
  let unsound = not . (^. predSound)
      
      tys = M.fromList $ map (\p -> ( p^.predName, ((p^.predSequential,p^.predPriority),p^.predType))) lst
      uns = S.fromList $ map (^.predName) $ filter unsound $ lst
      
      inferAll :: ((Substitution,ContextMap), [FlatPred], [FlatPred]) -> Choice ([FlatPred],(Substitution, ContextMap))
      inferAll (l, r, []) = return (r,l)
      inferAll (_ , r, p:_) | p^.predName == tipeName = throwTrace 0 $ tipeName++" can not be overloaded"
      inferAll ((lv,lt) , r, p:toplst) = do
        let fam = p^.predFamily
            b = p^.predSequential
            i = p^.predPriority
            nm = p^.predName
            val = p^.predValue
            ty = p^.predType
            kind = p^.predKind
            
        (ty,kind,lt) <- appendErr ("can not infer type for: "++nm++" : "++show ty) $ 
                            mtrace verbose "\nCompiling: type" $ vtrace 0 ("\t : " ++show ty ++"\n\t :: " ++show kind) $ 
                            typePipe verbose lt ((b,i),nm, generateBinding ty,kind) -- constrain the breadth first search to be local!
                            
        val <- case val of
          Just val -> appendErr ("can not infer type for: \n"++nm++" : "++show ty ++"\nnm = "++show val ) $ 
                      mtrace verbose "\nCompiling: value " $ vtrace 0 ("\t : " ++show val ++"\n\t:: " ++show ty) $ 
                      Just <$> typePipe verbose lt ((b,i),nm, generateBinding val,ty)                    
          Nothing -> return Nothing            
                      
        -- do the family check after ascription removal and typechecking because it can involve computation!
        unless (fam == Nothing || Just (getFamily ty) == fam)
          $ throwTrace 0 $ "not the right family: need "++show fam++" for "++nm ++ " = " ++show ty                    
          
        let resp = p & predType .~ ty 
                     & predKind .~ kind 
        inferAll $ case val of
          Just (val,_,_) -> ((M.insert nm val lv, sub' <$> lt), (resp & predValue .~ Just val) :r , sub <$> toplst) 
            where sub' (b,a) = (b, sub a)
                  sub :: (Show a, Subst a) => a -> a
                  sub = subst $ nm |-> ascribe val (dontcheck ty)
          _ -> ((lv, lt), resp:r, toplst)

  (lst',(lv,lt)) <- inferAll ((mempty,tys), [], topoSortAxioms True lst)
  
  let doubleCheckAll _ [] = return ()
      doubleCheckAll l (p:r) = do
        let nm = p^.predName
            val = p^.predType
            ty = p^.predKind
        
        let usedvars = freeVariables val `S.union` freeVariables ty `S.union` freeVariables val
        unless (S.isSubsetOf usedvars l)
          $ throwTrace 0 $ "Circular type:"
                        ++"\n\t"++nm++" : "++show val ++" : "++show ty
                        ++"\n\tcontains the following circular type dependencies: "
                        ++"\n\t"++show (S.toList $ S.difference usedvars l)
                        ++ "\nPossible Solution: declare it unsound"
                        ++ "\nunsound "++nm++" : "++show val
        doubleCheckAll (S.insert nm l) r
  
  doubleCheckAll (S.union envSet uns) $ topoSortAxioms False lst' 
  
  return $ (lv, snd <$> lt)

topoSortAxioms :: Bool -> [FlatPred] -> [FlatPred]
topoSortAxioms accountPot axioms = showRes $ topoSortComp (\p -> (p^.predName,) 
                                            $ showGraph (p^.predName)
                                            -- unsound can mean this causes extra cyclical things to occur
                                            $ (if accountPot && p^.predSound then S.union (getImplieds $ p^.predName) else id)
                                            $ S.fromList 
                                            $ filter (not . flip elem (map fst consts)) 
                                            $ S.toList $ freeVariables p ) axioms
                        
  where showRes a = vtrace 0 ("TOP_RESULT: "++show ((^.predName) <$> a)) a
        showGraph n a = vtrace 1 ("TOP_EDGE: "++n++" -> "++show a) a

        nm2familyLst  = catMaybes $ (\p -> (p^.predName,) <$> (p^.predFamily)) <$> axioms
        
        family2nmsMap = foldr (\(fam,nm) m -> M.insert nm (case M.lookup nm m of
                                  Nothing -> S.singleton fam
                                  Just s -> S.insert fam s) m
                                )  mempty nm2familyLst
        
        family2impliedsMap = M.fromList $ (\p -> (p^.predName, 
                                                  mconcat 
                                                  $ catMaybes 
                                                  $ map (`M.lookup` family2nmsMap) 
                                                  $ S.toList 
                                                  $ S.union (getImpliedFamilies $ p^.predType) (fromMaybe mempty $ freeVariables <$> p^.predValue)
                                                 )) <$> axioms
        
        getImplieds nm = fromMaybe mempty (M.lookup nm family2impliedsMap)

getImpliedFamilies s = S.intersection fs $ gif s
  where fs = freeVariables s
        gif (Spine "#imp_forall#" [ty,a]) = (case getFamilyM ty of
          Nothing -> id
          Just f | f == tipeName -> id
          Just f -> S.insert f) $ gif ty `S.union` gif a 
        gif (Spine a l) = mconcat $ gif <$> l
        gif (Abs _ ty l) = S.union (gif ty) (gif l)


typeCheckAll :: Bool -> [Decl] -> Choice [Decl]
typeCheckAll verbose preds = do
  
  (valMap, tyMap) <- typeCheckAxioms verbose $ toAxioms True preds
  
  let newPreds (Predicate t nm _ cs) = Predicate t nm (tyMap M.! nm) $ map (\(b,(nm,_)) -> (b,(nm, tyMap M.! nm))) cs
      newPreds (Query nm _) = Query nm (tyMap M.! nm)
      newPreds (Define t nm _ _) = Define t nm (valMap M.! nm) (tyMap M.! nm)
  
  return $ newPreds <$> preds

toAxioms :: Bool -> [Decl] -> [FlatPred]
toAxioms b = concat . zipWith toAxioms' [1..]
  where toAxioms' j (Predicate s nm ty cs) = 
          (FlatPred (PredData (Just $ tipeName) False j s) nm Nothing ty tipe)
          :zipWith (\(sequ,(nm',ty')) i -> (FlatPred (PredData (Just nm) sequ i False) nm' Nothing ty' tipe)) cs [0..]
        toAxioms' j (Query nm val) = [(FlatPred (PredData Nothing False j False) nm Nothing val tipe)]
        toAxioms' j (Define s nm val ty) = [ FlatPred (PredData Nothing False j s) nm (Just val) ty tipe]
                                           

  
toSimpleAxioms :: [Decl] -> ContextMap
toSimpleAxioms l = M.fromList $ (\p -> (p^.predName, ((p^.predSequential, p^.predPriority), p^.predType))) 
                   <$> toAxioms False l

solver :: ContextMap -> Type -> Either String [(Name, Term)]
solver axioms tp = case runError $ runRWST (search tp) (M.union envConsts axioms) emptyState of
  Right ((_,tm),_,_) -> Right $ [("query", tm)]
  Left s -> Left $ "reification not possible: "++s

reduceDecsByName :: [Decl] -> [Decl]
reduceDecsByName decs = map snd $ M.toList $ M.fromList $ map (\a -> (a ^. declName,a)) decs
