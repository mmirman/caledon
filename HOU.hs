{-# LANGUAGE  
 DeriveFunctor,
 FlexibleInstances,
 PatternGuards,
 UnicodeSyntax,
 TupleSections
 #-}
module HOU where

import Choice
import AST
import Context
import TopoSortAxioms
import Control.Monad.State (StateT, runStateT, modify, get)
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

vtrace0 = trace -- vtrace1
vtrace1 = vtrace2
vtrace2 = vtrace3
vtrace3 = const id

vtrace0throw s = vtrace0 s $ throwError s
vtrace1throw s = vtrace1 s $ throwError s
vtrace2throw s = vtrace2 s $ throwError s
vtrace3throw s = vtrace3 s $ throwError s
-----------------------------------------------
---  the higher order unification algorithm ---
-----------------------------------------------

flatten :: Constraint -> WithContext [SCons]
flatten (Bind quant nm ty c) = do
  modify $ addToTail quant nm ty
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

unify :: Constraint -> WithContext Substitution
unify cons = do
  cons <- lift $ regenAbsVars cons
  cons <- flatten cons
  let uniWhile :: Substitution -> [SCons] -> WithContext (Substitution, [SCons])
      uniWhile sub c' = do
        exists <- getExists        
            
        let c = reverse $ topoSort (heuristic $ M.keysSet exists) c'
            -- eventually we can make the entire algorithm a graph modification algorithm for speed, 
            -- such that we don't have to topologically sort every time.  Currently this only takes us from O(n log n) to O(n) per itteration, it is
            -- not necessarily worth it.
            uniWith wth backup = do
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
                Just (sub', c') -> do
                  let sub'' = sub *** sub'
                  modify $ subst sub'
                  uniWhile sub'' $! c'

        vtrace3 ("CONST: "++show c)
          ( uniWith unifyOne 
          $ uniWith unifySearch
          $ uniWith unifySearchAtom
          $ checkFinished c >> 
          return (sub, c))

  fst <$> uniWhile mempty cons



checkFinished [] = return ()
checkFinished cval = vtrace0throw $ "ambiguous constraint: " ++show cval

unifySearch :: SCons -> WithContext (Maybe (Substitution, [SCons]))
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

unifyOne :: SCons -> WithContext (Maybe (Substitution , [SCons]))
unifyOne (a :=: b) = do
  c' <- isolateForFail $ unifyEq $ a :=: b 
  case c' of 
    Nothing -> isolateForFail $ unifyEq $ b :=: a
    r -> return r
unifyOne _ = return Nothing

unifyEq cons@(a :=: b) = case (a,b) of 
  (Spine "#imp_forall#" [ty, l], b) -> vtrace1 "-implicit-" $ do
    a' <- lift $ getNewWith "@aL"
    modify $ addToTail Exists a' ty
    return $ Just (mempty, [rebuildSpine l [var a'] :=: b , var a' :@: ty])
  (b, Spine "#imp_forall#" [ty, l]) -> vtrace1 "-implicit-" $ do
    a' <- lift $ getNewWith "@aR"
    modify $ addToTail Exists a' ty
    return $ Just (mempty,  [b :=: rebuildSpine l [var a'] , var a' :@: ty])

  (Spine "#imp_abs#" (ty:l:r), b) -> vtrace1 ("-imp_abs- : "++show a ++ "\n\t"++show b) $ do
    a <- lift $ getNewWith "@iaL"
    modify $ addToTail Exists a ty
    return $ Just (mempty, [rebuildSpine l (var a:r) :=: b , var a :@: ty])
  (b, Spine "#imp_abs#" (ty:l:r)) -> vtrace1 "-imp_abs-" $ do
    a <- lift $ getNewWith "@iaR"
    modify $ addToTail Exists a ty
    return $ Just (mempty, [b :=: rebuildSpine l (var a:r) , var a :@: ty])

  (Spine "#tycon#" [Spine nm [_]], Spine "#tycon#" [Spine nm' [_]]) | nm /= nm' -> vtrace0throw $ "different type constraints: "++show cons
  (Spine "#tycon#" [Spine nm [val]], Spine "#tycon#" [Spine nm' [val']]) | nm == nm' -> 
    return $ Just (mempty, [val :=: val'])

  (Abs nm ty s , Abs nm' ty' s') -> vtrace1 "-aa-" $ do
    modify $ addToTail Forall nm ty
    return $ Just (mempty, [ty :=: ty' , s :=: subst (nm' |-> var nm) s'])
  (Abs nm ty s , s') -> vtrace1 "-as-" 
                      $ vtrace3 (show cons) $ do
    modify $ addToTail Forall nm ty
    return $ Just (mempty, [s :=: rebuildSpine s' [var nm]])

  (s, Abs nm ty s' ) -> vtrace1 "-as-" $ vtrace3 (show cons) $ do
    modify $ addToTail Forall nm ty
    return $ Just (mempty, [rebuildSpine s [var nm] :=: s'])

  (s , s') | s == s' -> vtrace1 "-eq-" $ return $ Just (mempty, [])
  (Spine x yl, s') -> do
    bind <- getElm ("all: "++show cons) x
    case bind of
      Left bind@Binding{ elmQuant = Exists } -> do
        raiseToTop bind (Spine x yl) $ \(a@(Spine x yl),ty) sub ->
          case subst sub s' of
            b@(Spine x' y'l) -> do
              bind' <- getElm ("gvar-blah: "++show cons) x'
              case bind' of
                Right ty' -> vtrace1 "-gc- " $ -- gvar-const
                  if allElementsAreVariables yl
                  then do 
                    a <- gvar_const (Spine x yl, ty) (Spine x' y'l, ty') 
                    vtrace3 ("-gc-ret- "++show a) $ return a
                  else return Nothing
                Left Binding{ elmQuant = Forall } | not $ S.member x' $ freeVariables yl -> vtrace1 "CANT: -gu-dep-" $ vtrace1throw $ "gvar-uvar-depends: "++show (a :=: b)
                Left Binding{ elmQuant = Forall } | S.member x $ freeVariables y'l -> 
                  vtrace0throw $ "CANT: occurs check: "++show (a :=: b)
                Left Binding{ elmQuant = Forall, elmType = ty' } ->vtrace1 "-gui-" $  -- gvar-uvar-inside
                  gvar_uvar_inside (Spine x yl, ty) (Spine x' y'l, ty')
                Left bind@Binding{ elmQuant = Exists, elmType = ty' } -> 
                  if not $ allElementsAreVariables yl && allElementsAreVariables y'l 
                  then return Nothing 
                  else if x == x' 
                       then vtrace1 "-ggs-" $ -- gvar-gvar-same
                         gvar_gvar_same (Spine x yl, ty) (Spine x' y'l, ty')
                       else -- gvar-gvar-diff
                         if S.member x $ freeVariables y'l 
                         then vtrace0throw $ "CANT: ggd-occurs check: "++show (a :=: b)
                         else vtrace1 ("-ggd- " ++show cons)
                              $ gvar_gvar_diff (Spine x yl, ty) (Spine x' y'l, ty') bind
            _ -> vtrace1 "-ggs-" $ return Nothing
      _ -> case s' of 
        b@(Spine x' _) | x /= x' -> do
          bind' <- getElm ("const case: "++show cons) x'
          case bind' of
            Left Binding{ elmQuant = Exists } -> return Nothing
            _ -> vtrace0throw ("CANT: -uud- two different universal equalities: "++show (a :=: b)) -- uvar-uvar 

        Spine x' yl' | x == x' -> vtrace1 ("-uue- ") $ vtrace3 (show (a :=: b)) $ do -- uvar-uvar-eq
          
          let match ((Spine "#tycon#" [Spine nm [a]]):al) bl = case findTyconInPrefix nm bl of
                Nothing -> match al bl
                Just (b,bl) -> ((a :=: b) :) <$> match al bl
          -- in this case we know that al has no #tycon#s in its prefix since we exhausted all of them in the previous case
              match al (Spine "#tycon#" [Spine _ [_]]:bl) = match al bl 
              match (a:al) (b:bl) = ((a :=: b) :) <$>  match al bl 
              match [] [] = return []
              match _ _ = vtrace0throw $ "CANT: different numbers of arguments on constant: "++show cons

          cons <- match yl yl'
          return $ Just (mempty, cons)
        _ -> vtrace0throw $ "CANT: uvar against a pi WITH CONS "++show cons
            
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
  x' <- lift $ getNewWith "@newx"
  
  let newx_args = map (var . fst) hl
      sub = x |-> Spine x' newx_args
      
      ty' = foldr (\(nm,ty) a -> forall nm ty a) ty hl
        
      addSub Nothing = return Nothing
      addSub (Just (sub',cons)) = do
        -- we need to solve subst twice because we might reify twice
        let sub'' = ((subst sub' <$> sub) *** sub') 

        modify $ subst sub'
        return $ Just (sub'', cons)
  modify $ removeFromContext x
  modify $ subst sub
  modify $ addToHead Exists x' ty' 
  
  -- now we can match against the right hand side
  r <- addSub =<< m (subst sub sp, ty') sub
  modify $ removeFromContext x'
  return r

      
getBase 0 a = a
getBase n (Spine "#forall#" [_, Abs _ _ r]) = getBase (n - 1) r
getBase _ a = a

makeBind xN us tyl arg = foldr (uncurry Abs) (Spine xN $ map var arg) $ zip us tyl

-- TODO: make sure this is correct.  its now just a modification of gvar_gvar_diff!
gvar_gvar_same (a@(Spine x yl), aty) (b@(Spine _ y'l), _) = do
  let n = length yl
                    
      (uNl,atyl) = unzip $ take n $ typeToListOfTypes aty
      
  xN <- lift $ getNewWith "@ggs"
  
  let perm = [iyt | (iyt,_) <- filter (\(_,(a,b)) -> a == b) $ zip (zip uNl atyl) (zip yl y'l) ]
      
      l = makeBind xN uNl atyl $ map fst perm
      
      xNty = foldr (uncurry forall) (getBase n aty) perm
      
      sub = x |-> l
      
  modify $ addToTail Exists xN xNty -- THIS IS DIFFERENT FROM THE PAPER!!!!
  
  
  return (Just (sub, [])) --var xN :@: xNty))
  
gvar_gvar_same _ _ = error "gvar-gvar-same is not made for this case"

gvar_gvar_diff (a',aty') (sp, _) bind = raiseToTop bind sp $ \(b'@(Spine x' y'l), bty) subO -> do
  let (Spine x yl, aty) = (subst subO a', subst subO aty')
      
      -- now x' comes before x 
      -- but we no longer care since I tested it, and switching them twice reduces to original
      n = length yl
      m = length y'l
                    
      (uNl,atyl) = unzip $ take n $ typeToListOfTypes aty
      (vNl,btyl) = unzip $ take m $ typeToListOfTypes bty
      
  xN <- lift $ getNewWith "@ggd"
  
  let perm = do
        (iyt,y) <- zip (zip uNl atyl) yl
        (i',_) <- filter (\(_,y') -> y == y') $ zip vNl y'l 
        return (iyt,i')
      
      l = makeBind xN uNl atyl $ map (fst . fst) perm
      l' = makeBind xN vNl btyl $ map snd perm
      
      xNty = foldr (uncurry forall) (getBase n aty) (map fst perm)
      
      sub = M.fromList [(x ,l), (x',l')]

  modify $ addToTail Exists xN xNty -- THIS IS DIFFERENT FROM THE PAPER!!!!
  
  vtrace3 ("SUBST: -ggd- "++show sub) $ return $ Just (sub, [])
  
gvar_uvar_inside a@(Spine _ yl, _) b@(Spine y _, _) = 
  case elemIndex (var y) $ reverse yl of
    Nothing -> return Nothing
    Just _ -> gvar_uvar_outside a b
gvar_uvar_inside _ _ = error "gvar-uvar-inside is not made for this case"
  
gvar_const a@(s@(Spine x yl), _) b@(s'@(Spine y _), bty) = vtrace3 (show a++"   ≐   "++show b) $
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
    x <- lift $ getNewWith "@xm"
    return (x, case j of
      Nothing -> Spine x vun
      Just a -> tycon a $ Spine x vun)  
      
  let toLterm (Spine "#forall#" [ty, Abs ui _ r]) = Abs ui ty $ toLterm r
      toLterm (Spine "#imp_forall#" [ty, Abs ui _ r]) = imp_abs ui ty $ toLterm r      
      toLterm _ = rebuildSpine (action vun) $ map snd xm
      
      l = toLterm aty
  
      vbuild e = foldr (\((_,nm),ty) a -> case ty of
                           Left ty -> forall nm ty a
                           Right ty -> imp_forall nm ty a
                       ) e untylr

      substBty sub (Spine "#forall#" [_, Abs vi bi r]) ((x,xi):xmr) = (x,vbuild $ subst sub bi)
                                                                :substBty (M.insert vi xi sub) r xmr
      substBty sub (Spine "#imp_forall#" [_, Abs vi bi r]) ((x,xi):xmr) = (x,vbuild $ subst sub bi)
                                                                    : substBty (M.insert vi xi sub) r xmr
      substBty _ _ [] = []
      substBty _ s l  = error $ "is not well typed: "++show s
                        ++"\nFOR "++show l 
                        ++ "\nON "++ show cons
      
      sub = x |-> l  -- THIS IS THAT STRANGE BUG WHERE WE CAN'T use x in the output substitution!
  
  modify $ flip (foldr ($)) $ uncurry (addToHead Exists) <$> substBty mempty bty xm  
  modify $ subst sub
  
  return $ Just (sub, [subst sub $ a :=: b])

gvar_fixed _ _ _ = error "gvar-fixed is not made for this case"

--------------------
--- proof search ---  
--------------------

-- need bidirectional search!
rightSearch m goal = vtrace1 ("-rs- "++show m++" ∈ "++show goal) $ case goal of
  Spine "#forall#" [a, b] -> do
    y <- lift $ getNewWith "@sY"
    x' <- lift $ getNewWith "@sX"
    let b' = rebuildSpine b [var x']
    modify $ addToTail Forall x' a        
    modify $ addToTail Exists y b'
    return $ Just [ var y :=: rebuildSpine m [var x'] , var y :@: b']

  Spine "#imp_forall#" [_, Abs x a b] -> do
    y <- lift $ getNewWith "@isY"
    x' <- lift $ getNewWith "@isX"
    let b' = subst (x |-> var x') b
    modify $ addToTail Forall x' a        
    modify $ addToTail Exists y b'
    return $ Just [ var y :=: rebuildSpine m [tycon x $ var x']
                  , var y :@: b'
                  ]
    
  l@(Spine nm _) -> do
    constants <- lift $ ask  
    foralls <- getForalls
    exists <- getExists        
    
    let env = M.union foralls constants
        envl = M.toList $ M.union (M.union foralls constants) exists
        
        notAbs (Abs _ _ _) = False
        notAbs _ = True
        
        sameFamily (_, Abs _ _ _) = False
        sameFamily ("pack",s) = "#exists#" == nm
        sameFamily (nm',s) = (M.notMember nm' exists || (notAbs m && nm' /= getFamily m)) 
                             && getFamily s == nm
        targets = filter sameFamily envl
    case targets of
      [] -> return Nothing
      _ -> if all (flip M.member env) $ S.toList (S.union (freeVariables m) (freeVariables l))
           then return $ Just []
           else if M.member nm exists 
                then return Nothing
                else Just <$> (F.asum $ (leftSearch m goal <$> reverse targets)) -- reversing works for now, but not forever!  need a heuristics + bidirectional search + control structures



leftSearch m goal (x,target) = vtrace1 ("LS: " ++ show m ++" ∈ "++ show goal
                                        ++"\n\t@ " ++x++" : " ++show target)
                             $ leftCont (var x) target
  where leftCont n target = vtrace3throw ("LS: " ++ show m ++" ∈ "++ show goal
                                        ++"\n\t@ " ++x++" : " ++show target) <|> case target of
          Spine "#forall#" [a, b] -> do
            x' <- lift $ getNewWith "@sla"
            modify $ addToTail Exists x' a
            cons <- leftCont (rebuildSpine n [var x']) (rebuildSpine b [var x'])
            return $ cons++[var x' :@: a]

          Spine "#imp_forall#" [_ , Abs x a b] -> do  
            x' <- lift $ getNewWith "@isla"
            modify $ addToTail Exists x' a
            cons <- leftCont (rebuildSpine n [tycon x $ var x']) (subst (x |-> var x') b)
            return $ cons++[var x' :@: a]
          Spine _ _ -> do
            return $ [goal :=: target , m :=: n]
          _ -> error $ "λ does not have type atom: " ++ show target

search :: Type -> WithContext (Substitution, Term)
search ty = do
  e <- lift $ getNewWith "@e"
  sub <- unify $ (∃) e ty $ SCons [var e :@: ty]
  return $ (sub, subst sub $ var e)

-----------------------------
--- constraint generation ---
-----------------------------

(≐) a b = lift $ tell $ SCons [a :=: b]
(.@.) a b = lift $ tell $ SCons [a :@: b]

-- TODO: flatten constraints here for even more speed (never should we have to deal with the heirarchy)!
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
                (tycon nm (var x):) <$> (chop (subst (nm |-> var x) tyv) lst)

            Just (val,l) -> do
              val <- checkType val ty'
              (tycon nm val:) <$> chop (subst (nm |-> val) tyv) l
          Spine "#forall#" [ty', c] -> do
            a <- checkType a ty'
            (a:) <$> chop (rebuildSpine c [a]) l
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

    mty <- (M.lookup head) <$> lift ask
    
    case mty of 
      Nothing -> lift $ vtrace0throw $ "variable: "++show head++" not found in the environment."
                                     ++ "\n\t from "++ show sp
                                     ++ "\n\t from "++ show ty
      Just ty' -> Spine head <$> chop ty' args

----------------------
--- type inference ---
----------------------
typeInfer :: Constants -> (Name,Spine,Type) -> Choice Constants
typeInfer env (nm,val,ty) = (\r -> (\(a,_,_) -> a) <$> runRWST r (M.union envConsts env) 0) $ do

  (val,constraint) <- appendErr ("in name: "++nm++" : "++show val) $ 
                      trace ("Checking: " ++nm) $ 
                      vtrace0 ("\tVAL: " ++show val) $ 
                      vtrace0 ("\t:: " ++show ty) $ 
                      typeCheckToEnv $ checkType val ty
  (sub,ctxt) <- runStateT (unify constraint) emptyContext
  
  let res = unsafeSubst sub val
  vtrace0 ("RESULT: "++nm++" : "++show res) $
      return $ M.insert nm res env

unsafeSubst s (Spine nm apps) = let apps' = unsafeSubst s <$> apps in case s ! nm of 
  Just nm -> rebuildSpine nm apps'
  _ -> Spine nm apps'
unsafeSubst s (Abs nm tp rst) = Abs nm (unsafeSubst s tp) (unsafeSubst s rst)
  
----------------------------
--- the public interface ---
----------------------------
typeCheckAxioms :: [(Maybe Name,Name,Spine,Type)] -> Choice Constants
typeCheckAxioms lst = do
  
  -- check the closedness of families.  this gets done
  -- after typechecking since family checking needs to evaluate a little bit
  -- in order to allow defs in patterns
  let inferAll (l , []) = return l
      inferAll (l , (fam,nm,val,ty):toplst) = do
        
        unless (fam == Nothing || Just (getFamily val) == fam)
          $ vtrace0throw $ "not the right family: need "++show fam++" for "++nm ++ " = " ++show val
        
        l' <- appendErr ("can not infer type for: "
                        ++"\nWITH: "++nm++ " : "++show ty
                        ++"\nAS:   "++nm++ " = "++show val
                        ) $ 
              typeInfer l (nm, val,ty) -- constrain the breadth first search to be local! 
        inferAll $ case nm of
          '#':'v':':':nm' -> (subst sub <$> l', (\(fam,nm,val,ty) -> (fam,nm, subst sub val, subst sub ty)) <$> toplst) 
            where sub = nm' |-> (l' M.! nm)                                   
          _ -> (l', toplst)
        
  inferAll (mempty, topoSortAxioms lst)
  
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
solver axioms tp = case runError $ runRWST (runStateT (search tp) emptyContext) (M.union envConsts $ M.fromList axioms) 0 of
  Right (((s,tm),_),_,_) -> Right $ [("query", tm)] -- :M.toList s
  Left s -> Left $ "reification not possible: "++s
