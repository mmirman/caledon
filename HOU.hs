{-# LANGUAGE  
 DeriveFunctor,
 FlexibleInstances,
 PatternGuards,
 UnicodeSyntax,
 TupleSections,
 BangPatterns
 #-}
module HOU where

import Choice
import AST
import Context
import TopoSortAxioms
import Control.Monad.State (StateT, forM_,runStateT, modify, get)
import Control.Monad.RWS (RWST, runRWST, ask, tell)
import Control.Monad.Error (throwError, MonadError)
import Control.Monad (unless, forM, replicateM, void)
import Control.Monad.Trans (lift)
import Control.Applicative
import qualified Data.Foldable as F
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace

import System.IO.Unsafe

{-# INLINE level #-}
level = 0

{-# INLINE vtrace #-}
vtrace !i | i < level = trace
vtrace !i = const id

{-# INLINE vtraceShow #-}
vtraceShow !i1 !i2 s v | i2 < level = trace $ s ++" : "++show v
vtraceShow !i1 !i2 s v | i1 < level = trace s
vtraceShow !i1 !i2 s v = id

{-# INLINE throwTrace #-}
throwTrace !i s = vtrace i s $ throwError s


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

heuristic exists (a :@: b) = (nm , edges)
  where searches = S.intersection (freeVariables a) exists
        satisfying = S.intersection (freeVariables b) exists
        nm = case S.toList satisfying of
          [] -> getFamily b
          a:_ -> a
        edges = searches
heuristic exists (a :=: b) = ("##"++show a++":=:"++show b, mempty)

unify :: Constraint -> Env Substitution
unify cons = do
  cons <- regenAbsVars cons
  cons <- flatten cons
  let uniWhile :: Substitution -> [SCons] -> Env (Substitution, [SCons])
      uniWhile !sub !c' = do
        exists <- getExists        
        c' <- regenAbsVars c'          
        let c = c' -- reverse $ topoSort (heuristic $ M.keysSet exists) c'
            -- eventually we can make the entire algorithm a graph modification algorithm for speed, 
            -- such that we don't have to topologically sort every time.  Currently this only takes us from O(n log n) to O(n) per itteration, it is
            -- not necessarily worth it.
            uniWith !wth !backup = do
              let searchIn [] r = return Nothing
                  searchIn (next:l) r = do
                    c1' <- wth next 
                    case c1' of
                      Just (sub',next') -> return $ Just (sub', (subst sub' $ reverse r)++
                                                                next'
                                                                ++subst sub' l)
                      Nothing -> searchIn l (next:r)
              res <- searchIn c []
              case res of
                Nothing -> do
                  backup
                Just (!sub', c') -> do
                  let !sub'' = sub *** sub'
                  modifyCtxt $ subst sub'
                  uniWhile sub'' $! c'

        vtrace 3 ("CONST: "++show c)
          ( uniWith unifyOne 
          $ uniWith unifySearch
          $ uniWith unifySearchAtom
          $ checkFinished c >> 
          return (sub, c))

  fst <$> uniWhile mempty cons



checkFinished [] = return ()
checkFinished cval = throwTrace 0 $ "ambiguous constraint: " ++show cval

unifySearch :: SCons -> Env (Maybe (Substitution, [SCons]))
unifySearch (a :@: b) | b /= var "atom" = do
  cons <- rightSearch a b
  return $ case cons of
    Nothing -> Nothing
    Just cons -> Just (mempty, cons)
unifySearch _ = return Nothing

unifySearchAtom (a :@: b) = do
  cons <- rightSearch a b
  return $ case cons of
    Nothing -> Nothing
    Just cons -> Just (mempty, cons)
unifySearchAtom _ = return Nothing

unifyOne :: SCons -> Env (Maybe (Substitution , [SCons]))
unifyOne (a :=: b) = do
  c' <- isolateForFail $ unifyEq $ a :=: b 
  case c' of 
    Nothing -> isolateForFail $ unifyEq $ b :=: a
    r -> return r
unifyOne _ = return Nothing

unifyEq cons@(a :=: b) = case (a,b) of 
  (Spine "#imp_forall#" [ty, l], b) -> vtrace 1 "-implicit-" $ do
    a' <- getNewWith "@aL"
    modifyCtxt $ addToTail "-implicit-" Exists a' ty
    return $ Just (mempty, [l `apply` var a' :=: b , var a' :@: ty])
  (b, Spine "#imp_forall#" [ty, l]) -> vtrace 1 "-implicit-" $ do
    a' <- getNewWith "@aR"
    modifyCtxt $ addToTail "-implicit-" Exists a' ty
    return $ Just (mempty,  [b :=: l `apply` var a' , var a' :@: ty])

  (Spine "#imp_abs#" (ty:l:r), b) -> vtrace 1 ("-imp_abs- : "++show a ++ "\n\t"++show b) $ do
    a <- getNewWith "@iaL"
    modifyCtxt $ addToTail "-imp_abs-" Exists a ty
    return $ Just (mempty, [rebuildSpine l (var a:r) :=: b , var a :@: ty])
  (b, Spine "#imp_abs#" (ty:l:r)) -> vtrace 1 "-imp_abs-" $ do
    a <- getNewWith "@iaR"
    modifyCtxt $ addToTail "-imp_abs-" Exists a ty
    return $ Just (mempty, [b :=: rebuildSpine l (var a:r) , var a :@: ty])

  (Spine "#tycon#" [Spine nm [_]], Spine "#tycon#" [Spine nm' [_]]) | nm /= nm' -> throwTrace 0 $ "different type constraints: "++show cons
  (Spine "#tycon#" [Spine nm [val]], Spine "#tycon#" [Spine nm' [val']]) | nm == nm' -> 
    return $ Just (mempty, [val :=: val'])

  (Abs nm ty s , Abs nm' ty' s') -> vtrace 1 "-aa-" $ do
    modifyCtxt $ addToTail "-aa-" Forall nm ty
    return $ Just (mempty, [ty :=: ty' , s :=: subst (nm' |-> var nm) s'])
  (Abs nm ty s , s') -> vtraceShow 1 2 "-asL-" cons $ do
    modifyCtxt $ addToTail "-asL-" Forall nm ty
    return $ Just (mempty, [s :=: s' `apply` var nm])

  (s, Abs nm ty s' ) -> vtraceShow 1 2 "-asR-" cons $ do
    modifyCtxt $ addToTail "-asR-" Forall nm ty
    return $ Just (mempty, [s `apply` var nm :=: s'])

  (s , s') | s == s' -> vtrace 1 "-eq-" $ return $ Just (mempty, [])
  (s@(Spine x yl), s') -> vtrace 4 "-ss-" $ do
    bind <- getElm ("all: "++show cons) x
    case bind of
      Left bind@Binding{ elmQuant = Exists } -> vtrace 4 "-g?-" $ do
        raiseToTop bind (Spine x yl) $ \(a@(Spine x yl),ty) sub ->
          case subst sub s' of
            b@(Spine x' y'l) -> vtrace 4 "-gs-" $ do
              bind' <- getElm ("gvar-blah: "++show cons) x'
              case bind' of
                Right ty' -> vtraceShow 1 2 "-gc-" cons $ -- gvar-const
                  --if allElementsAreVariables yl
                  --then gvar_const (Spine x yl, ty) (Spine x' y'l, ty')  
                  -- else return Nothing
                  gvar_const (Spine x yl, ty) (Spine x' y'l, ty') 
                Left Binding{ elmQuant = Forall } | not $ S.member x' $ freeVariables yl -> 
                  throwTrace 0 $ "CANT: gvar-uvar-depends: "++show (a :=: b)
                Left Binding{ elmQuant = Forall } | S.member x $ freeVariables y'l -> 
                  throwTrace 0 $ "CANT: occurs check: "++show (a :=: b)
                Left Binding{ elmQuant = Forall, elmType = ty' } -> vtrace 1 "-gui-" $  -- gvar-uvar-inside
                  gvar_uvar_inside (Spine x yl, ty) (Spine x' y'l, ty')
                Left bind@Binding{ elmQuant = Exists, elmType = ty' } -> 
                  if not $ allElementsAreVariables yl && allElementsAreVariables y'l 
                  then return Nothing 
                  else if x == x' 
                       then vtraceShow 1 2 "-ggs-" cons $ -- gvar-gvar-same
                         gvar_gvar_same (Spine x yl, ty) (Spine x' y'l, ty')
                       else -- gvar-gvar-diff
                         if S.member x $ freeVariables y'l 
                         then throwTrace 0 $ "CANT: ggd-occurs check: "++show (a :=: b)
                         else vtraceShow 1 2 "-ggd-" cons $ gvar_gvar_diff (Spine x yl, ty) (Spine x' y'l, ty') bind
            _ -> vtrace 1 "-ggs-" $ return Nothing
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
              match _ _ = throwTrace 0 $ "CANT: different numbers of arguments on constant: "++show cons

          cons <- match yl yl'
          return $ Just (mempty, cons)
        _ -> throwTrace 0 $ "CANT: uvar against a pi WITH CONS "++show cons
            
allElementsAreVariables :: [Spine] -> Bool
allElementsAreVariables = all $ \c -> case c of
  Spine _ [] -> True
  _ -> False

typeToListOfTypes (Spine "#forall#" [_, Abs x ty l]) = (x,ty):typeToListOfTypes l
typeToListOfTypes (Spine _ _) = []
typeToListOfTypes a@(Abs _ _ _) = error $ "not a type" ++ show a

-- the problem WAS (hopefully) here that the binds were getting
-- a different number of substitutions than the constraints were.
-- make sure to check that this is right in the future.
raiseToTop bind@Binding{ elmName = x, elmType = ty } sp m = do
  
  hl <- reverse <$> getBindings bind
  x' <- getNewWith "@newx"
  
  let newx_args = map (var . fst) hl
      sub = x |-> Spine x' newx_args
      
      ty' = foldr (\(nm,ty) a -> forall nm ty a) ty hl
        
      addSub Nothing = return Nothing
      addSub (Just (sub',cons)) = do
        -- we need to solve subst twice because we might reify twice
        let sub'' = ((subst sub' <$> sub) *** sub') 

        modifyCtxt $ subst sub'
        return $ Just (sub'', cons)
        
  modifyCtxt $ addToHead "-rtt-" Exists x' ty' . removeFromContext x
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
      
  modifyCtxt $ addToHead "-ggs-" Exists xN xNty -- THIS IS DIFFERENT FROM THE PAPER!!!!
  
  return $ Just (sub, []) -- var xN :@: xNty])
  
gvar_gvar_same _ _ = error "gvar-gvar-same is not made for this case"

gvar_gvar_diff (a',aty') (sp, _) bind = raiseToTop bind sp $ \(b'@(Spine x' y'l), bty) subO -> do
  
  let (Spine x yl, aty) = (subst subO a', subst subO aty')

      -- now x' comes before x 
      -- but we no longer care since I tested it, and switching them twice reduces to original
      n = length yl
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
      
      sub = M.fromList [(x ,l), (x',l')]

  modifyCtxt $ addToHead "-ggd-" Exists xN xNty -- THIS IS DIFFERENT FROM THE PAPER!!!!
  
  vtrace 3 ("SUBST: -ggd- "++show sub) $ return $ Just (sub, []) -- var xN :@: xNty])
  
gvar_uvar_inside a@(Spine _ yl, _) b@(Spine y _, _) = 
  case elemIndex (var y) $ reverse yl of
    Nothing -> return Nothing
    Just _ -> gvar_uvar_outside a b
gvar_uvar_inside _ _ = error "gvar-uvar-inside is not made for this case"
  
gvar_const a@(s@(Spine x yl), _) b@(s'@(Spine y _), bty) = vtrace 3 (show a++"   ≐   "++show b) $
  case elemIndex (var y) $ yl of 
    Nothing -> gvar_fixed a b $ var . const y
    Just _ -> do
     gvar_uvar_outside a b <|> gvar_fixed a b (var . const y) 

gvar_const _ _ = error "gvar-const is not made for this case"

gvar_uvar_outside a@(s@(Spine x yl),_) b@(s'@(Spine y _),bty) = do
  let ilst = [i | (i,y') <- zip [0..] yl , y' == var y] 
  i <- F.asum $ return <$> ilst
  gvar_fixed a b $ (!! i) 


gvar_uvar_outside _ _ = error "gvar-uvar-outside is not made for this case"

getTyNews (Spine "#forall#" [_, Abs _ _ t]) = Nothing:getTyNews t
getTyNews (Spine "#imp_forall#" [_, Abs nm _ t]) = Just nm:getTyNews t
getTyNews _ = []

gvar_fixed (a@(Spine x _), aty) (b@(Spine _ y'l), bty) action = do
  let m = getTyNews bty -- max (length y'l) (getTyLen bty)
      cons = a :=: b
--      getNewTys "@xm" bty 

  
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

      substBty sub (Spine "#forall#" [_, Abs vi bi r]) ((x,xi):xmr) = (x,vbuild $ subst sub bi)
                                                                :substBty (M.insert vi (fst xi) sub) r xmr
      substBty sub (Spine "#imp_forall#" [_, Abs vi bi r]) ((x,xi):xmr) = (x,vbuild $ subst sub bi)
                                                                    : substBty (M.insert vi (fst xi) sub) r xmr
      substBty _ _ [] = []
      substBty _ s l  = error $ "is not well typed: "++show s
                        ++"\nFOR "++show l 
                        ++ "\nON "++ show cons
      
      sub = x |-> l -- THIS IS THAT STRANGE BUG WHERE WE CAN'T use x in the output substitution!
      addExists s t = vtrace 3 ("adding: "++show s++" ::: "++show t) $ addToHead "-gf-" Exists s t
  modifyCtxt $ flip (foldr ($)) $ uncurry addExists <$> substBty mempty bty xm  
  modifyCtxt $ subst sub
  
  return $ Just (sub, [subst sub $ a :=: b])

gvar_fixed _ _ _ = error "gvar-fixed is not made for this case"

--------------------
--- proof search ---  
--------------------


-- need bidirectional search!
rightSearch m goal = vtrace 1 ("-rs- "++show m++" ∈ "++show goal) $ 
  case goal of
    Spine "#forall#" [a, b] -> do
      y <- getNewWith "@sY"
      x' <- getNewWith "@sX"
      let b' = b `apply` var x'
      modifyCtxt $ addToTail "-rsFf-" Forall x' a
      modifyCtxt $ addToTail "-rsFe-" Exists y b'
      return $ Just [ var y :=: m `apply` var x' , var y :@: b']

    Spine "#imp_forall#" [_, Abs x a b] -> do
      y <- getNewWith "@isY"
      x' <- getNewWith "@isX"
      let b' = subst (x |-> var x') b
      modifyCtxt $ addToTail "-rsIf-" Forall x' a        
      modifyCtxt $ addToTail "-rsIe-" Exists y b'
      return $ Just [ var y :=: m `apply` (tycon x $ var x')
                    , var y :@: b'
                    ]
    Spine "putChar" [c@(Spine ['\'',l,'\''] [])] ->
      case unsafePerformIO $ putStr $ l:[] of
        () -> return $ Just [ m :=: Spine "putCharImp" [c]]
    Spine "putChar" [_] -> vtrace 0 "FAILING PUTCHAR" $ return Nothing
  
    Spine "readLine" [l] -> 
      case toNCCstring $ unsafePerformIO $ getLine of
        !s -> do
          y <- getNewWith "@isY"
          let ls = l `apply` s
          modifyCtxt $ addToTail "-rl-" Exists y ls
          return $ Just [m :=: Spine "readLineImp" [l,s, var y], var y :@: Spine "run" [ls]]
    Spine nm _ -> do
      constants <- getConstants
      foralls <- getForalls
      exists <- getExists
      let env = M.union foralls constants
      
          isFixed a = isChar a || M.member a env
      
          getFixedType a | isChar a = Just $ var "char"
          getFixedType a = M.lookup a env
      
      let mfam = case m of 
            Abs _ _ _ -> Nothing
            Spine nm _ -> case getFixedType nm of
              Just t -> Just (nm,t)
              Nothing -> Nothing
  
          sameFamily (_, Abs _ _ _) = False
          sameFamily ("pack",s) = "#exists#" == nm
          sameFamily (_,s) = getFamily s == nm
          
      targets <- case mfam of
        Just (nm,t) -> return $ [(nm,t)]
        Nothing -> do
--          let excludes = S.toList $ S.intersection (M.keysSet exists) $ freeVariables m
--          searchMaps <- mapM getVariablesBeforeExists excludes
          
          let searchMap = env {- M.union env $ case searchMaps of
                [] -> mempty
                a:l -> foldr (M.intersection) a l -}
                
          return $ filter sameFamily $ M.toList searchMap
      
      if all isFixed $ S.toList $ S.union (freeVariables m) (freeVariables goal)
        then return $ Just []
        else case targets of
          [] -> return Nothing
          _  -> Just <$> (F.asum $ (leftSearch m goal <$> reverse targets)) -- reversing works for now, but not forever!  need a heuristics + bidirectional search + control structures

a .-. s = foldr (\k v -> M.delete k v) a s 

leftSearch m goal (x,target) = vtrace 1 ("LS: " ++ show m ++" ∈ "++ show goal
                                        ++"\n\t@ " ++x++" : " ++show target)
                             $ leftCont (var x) target
  where leftCont n target = throwTrace 3 ("DEFER: LS: " ++ show m ++" ∈ "++ show goal
                                        ++"\n\t@ " ++x++" : " ++show target) <|> case target of
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
            return $ [goal :=: target , m :=: n]
          _ -> error $ "λ does not have type atom: " ++ show target

search :: Type -> Env (Substitution, Term)
search ty = do
  e <- getNewWith "@e"
  sub <- unify $ (∃) e ty $ SCons [var e :@: ty]
  return $ (sub, subst sub $ var e)

-----------------------------
--- constraint generation ---
-----------------------------

(≐) a b = lift $ tell $ SCons [a :=: b]
(.@.) a b = lift $ tell $ SCons [a :@: b]

checkType :: Spine -> Type -> TypeChecker Spine
checkType sp ty = case sp of
  Spine "#ascribe#" (t:v:l) -> do
    v <- checkType v t
    checkType (rebuildSpine v l) ty
  
  Spine "#infer#" [_, Abs x tyA tyB ] -> do
    tyA <- checkType tyA atom
    x' <- getNewWith "@inf"
    addToEnv (∃) x' tyA $ do
      var x' .@. tyA
      checkType (subst (x |-> var x') tyB) ty

  Spine "#imp_forall#" [_, Abs x tyA tyB] -> do
    tyA <- checkType tyA atom
    tyB <- addToEnv (∀) x tyA $ checkType tyB atom
    ty ≐ atom
    return $ imp_forall x tyA tyB
    
  Spine "#forall#" [_, Abs x tyA tyB] -> do
    tyA <- checkType tyA atom
    tyB <- addToEnv (∀) x tyA $ checkType tyB atom
    ty ≐ atom
    return $ forall x tyA tyB

  -- below are the only cases where bidirectional type checking is useful 
  Spine "#imp_abs#" [_, Abs x tyA sp] -> case ty of
    Spine "#imp_forall#" [_, Abs x' tyA' tyF'] -> do
      tyA <- checkType tyA atom
      tyA ≐ tyA'
      addToEnv (∀) x tyA $ do
        imp_abs x tyA <$> checkType sp (subst (x' |-> var x) tyF')
    _ -> do
      e <- getNewWith "@e"
      tyA <- checkType tyA atom
      addToEnv (∃) e (forall x tyA atom) $ do
        imp_forall x tyA (Spine e [var x]) ≐ ty
        sp <- addToEnv (∀) x tyA $ checkType sp (Spine e [var x])
        return $ imp_abs x tyA sp

  Abs x tyA sp -> case ty of
    Spine "#forall#" [_, Abs x' tyA' tyF'] -> do
      tyA <- checkType tyA atom
      tyA ≐ tyA'
      addToEnv (∀) x tyA $ do
        Abs x tyA <$> checkType sp (subst (x' |-> var x) tyF')
    _ -> do
      e <- getNewWith "@e"
      tyA <- checkType tyA atom
      addToEnv (∃) e (forall x tyA atom) $ do
        forall x tyA (Spine e [var x]) ≐ ty
        Abs x tyA <$> (addToEnv (∀) x tyA $ checkType sp (Spine e [var x]))
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
                ( tycon nm (var x):) <$> (chop (subst (nm |-> var x) tyv) lst)

            Just (val,l) -> do
              val <- checkType val ty'
              (tycon nm val:) <$> chop (subst (nm |-> val) tyv) l
          Spine "#forall#" [ty', c] -> do
            a <- checkType a ty'
            (a:) <$> chop (c `apply` a) l
          _ -> do  
            x <- getNewWith "@xin"
            z <- getNewWith "@zin"
            tybody <- getNewWith "@v"
            let tybodyty = forall z (var x) atom
            addToEnv (∃) x atom $ addToEnv (∃) tybody tybodyty $ do 
              a <- checkType a (var x)
              v <- getNewWith "@v"
              forall v (var x) (Spine tybody [var v]) ≐ mty
              (a:) <$> chop (Spine tybody [a]) l

    mty <- (M.lookup head) <$> lift getFullCtxt
    
    case mty of 
      Nothing -> lift $ throwTrace 0 $ "variable: "++show head++" not found in the environment."
                                     ++ "\n\t from "++ show sp
                                     ++ "\n\t from "++ show ty
      Just ty' -> Spine head <$> chop ty' args

checkFullType :: Spine -> Type -> Env (Spine, Constraint)
checkFullType val ty = typeCheckToEnv $ checkType val ty

----------------------
--- type inference ---
----------------------
initInfers :: Spine -> ([(String,Spine)],Spine)
initInfers (Spine "#infer#" [ty, Abs nm' _ v]) = (lst++(nm',ty'):lst' , v')
  where (lst , ty') = initInfers ty
        (lst' , v') = initInfers v
initInfers (Spine c l) = (concat insts, Spine c l')
  where (insts,l') = unzip $ map initInfers l
initInfers (Abs nm ty r) = (l1++l2, Abs nm ty' r')
  where (l1,ty') = initInfers ty
        (l2,r') = initInfers r
        
-- this is entirely correct, but way slow on bigger programs!
fullProgramInfer :: [(Maybe Name,Name,Spine,Type)] -> Choice ContextMap
fullProgramInfer lst = (\r -> (\(a,_,_) -> a) <$> runRWST r envConsts emptyState) $ do
  lst <- return $ topoSortAxioms lst
  
  forM_ lst $ \(_,nm,val,ty) -> do
    let (exis,val') = initInfers val
        
    forM_ exis $ \(nm,v) -> do
      modifyCtxt $ addToTail "-fpi-" Exists nm v
    modifyCtxt $ addToTail "-fpip-" Forall nm val'
  
  cons <- forM lst $ \(_,nm,val,ty) -> do

    val :@: ty <- regenAbsVars $ val :@: ty
    (sp,cons) <- checkFullType val ty
    return ((nm,sp), cons)
    
  let (lst,conses) = unzip cons
      constraint = foldr (\(nm,ty) b -> (∀) nm ty b) (mconcat conses) lst
    
  sub <- unify constraint
  
  return $ M.fromList $ map (\(n,v) -> (n,unsafeSubst sub v)) lst

typeInfer :: ContextMap -> (Name,Spine,Type) -> Choice (Term,ContextMap)
typeInfer env (nm,val,ty) = (\r -> (\(a,_,_) -> a) <$> runRWST r (M.union envConsts env) emptyState) $ do
  val <- return $ alphaConvert mempty val
  (val,mem) <- regenWithMem val
  
  (val,constraint) <- appendErr ("in name: "++nm++" : "++show val) $ 
                      trace ("Checking: " ++nm) $ 
                      vtrace 0 ("\tVAL: " ++show val  
                                ++"\n\t:: " ++show ty) $ checkFullType val ty
  sub <- unify constraint
  
  let res = rebuildFromMem mem $ unsafeSubst sub val

  vtrace 0 ("RESULT: "++nm++" : "++show res) $
      return $ (res, M.insert nm res env)

unsafeSubst s (Spine nm apps) = let apps' = unsafeSubst s <$> apps in case s ! nm of 
  Just nm -> rebuildSpine nm apps'
  _ -> Spine nm apps'
unsafeSubst s (Abs nm tp rst) = Abs nm (unsafeSubst s tp) (unsafeSubst s rst)
  
----------------------------
--- the public interface ---
----------------------------
typeCheckAxioms :: [(Maybe Name,Name,Spine,Type)] -> Choice ContextMap
typeCheckAxioms lst = do
  
  -- check the closedness of families.  this gets done
  -- after typechecking since family checking needs to evaluate a little bit
  -- in order to allow defs in patterns
  let notval (_,'#':'v':':':_,_,_) = False
      notval _ = True
      
      tys = M.fromList $ map (\(_,nm,ty,_) -> (nm,ty)) $ filter notval lst
      
      inferAll (l , []) = return l
      inferAll (l , (fam,nm,val,ty):toplst) = do

        (val,l') <- appendErr ("can not infer type for: "
                               ++"\nWITH: "++nm++ " : "++show ty
                               ++"\nAS:   "++nm++ " = "++show val
                              ) $ 
                    typeInfer (tys *** l) (nm, val,ty) -- constrain the breadth first search to be local!
                    
        -- do the family check after ascription removal and typechecking because it can involve computation!
        unless (fam == Nothing || Just (getFamily val) == fam)
          $ throwTrace 0 $ "not the right family: need "++show fam++" for "++nm ++ " = " ++show val        
          
        inferAll $ case nm of
          '#':'v':':':nm' -> (subst sub <$> l', (\(fam,nm,val,ty) -> (fam,nm,subst sub val, subst sub ty)) <$> toplst) 
            where sub = nm' |-> val  -- the ascription isn't necessary because we don't have unbound variables
          _ -> (l', toplst)

  l <- inferAll (mempty, topoSortAxioms lst)
  return l 
  
typeCheckAll :: [Predicate] -> Choice [Predicate]
typeCheckAll preds = do
  let toAxioms (Predicate nm ty cs) = (Just "atom",nm,ty,atom):map (\(nm',ty') -> (Just nm,nm',ty',atom)) cs
      toAxioms (Query nm val) = [(Nothing, nm,val,atom)]
      toAxioms (Define nm val ty) = [(Nothing, nm,ty,atom), (Nothing, "#v:"++nm,val,ty)]
  tyMap <- typeCheckAxioms $ concatMap toAxioms preds
  
  let newPreds (Predicate nm _ cs) = Predicate nm (tyMap M.! nm) $ map (\(nm,_) -> (nm,tyMap M.! nm)) cs
      newPreds (Query nm _) = Query nm (tyMap M.! nm)
      newPreds (Define nm _ _) = Define nm (tyMap M.! ("#v:"++nm)) (tyMap M.! nm)
  
  return $ newPreds <$> preds
  
solver :: [(Name,Type)] -> Type -> Either String [(Name, Term)]
solver axioms tp = case runError $ runRWST (search tp) (M.union envConsts $ M.fromList axioms) emptyState of
  Right ((_,tm),_,_) -> Right $ [("query", tm)]
  Left s -> Left $ "reification not possible: "++s
