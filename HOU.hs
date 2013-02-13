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

vtrace0 = vtrace1
vtrace1 = vtrace2
vtrace2 = vtrace3
vtrace3 = trace -- const id

-----------------------------------------------
---  the higher order unification algorithm ---
-----------------------------------------------

unify :: Constraint -> WithContext Substitution
unify cons = do
  cons <- lift $ regenAbsVars cons
  let uniWhile c = uniWith unifyOne 
                 $ uniWith unifySearch
--                 $ uniWith envSearch
                 $ --checkFinished c >>
                 return (mempty, c)
        where uniWith wth backup = do
                res <- wth c 
                case res of
                  Nothing -> backup
                  Just (sub, c') -> do
                    modify $ subst sub
                    (\(s,c) -> (sub *** s, c)) <$> uniWhile (reduceTops c')
  fst <$> uniWhile cons


reduceTops (c1 :&: c2) = case (reduceTops c1, reduceTops c2) of
  (Top,b) -> b
  (a,Top) -> a
  (a,b) -> a :&: b
reduceTops (Bind Exists nm ty b) = Bind Exists nm ty $ reduceTops b 
reduceTops (Bind Forall nm ty b) = case reduceTops b of
  Top -> Top
  b -> Bind Forall nm ty b
reduceTops r = r

checkFinished cval = do
  let cf c = case c of
          Top -> return ()
          Bind Forall _ _ c -> cf c
          c1 :&: c2 -> cf c1 >> cf c2
          _ -> throwError $ "ambiguous constraint: " ++show cval
  
  binds <- getAnExist
  unless (binds == Nothing) $ throwError $ "ambiguous constraint: " ++show cval
  cf cval
  
unifySearch (a :@: b) = do
  cons <- rightSearch a b
  return $ Just (mempty, cons)
unifySearch r = unifyOther unifySearch r

unifyOther wth (Bind quant nm ty c) = do
  modify $ addToTail quant nm ty
  return $ Just (mempty, c)
unifyOther wth (c1 :&: c2) = do
  c1' <- wth c1 
  case c1' of
    Nothing -> do 
      c2' <- wth c2
      return $ case c2' of
        Nothing -> Nothing
        Just (sub,c2) -> Just $ (sub, subst sub c1 :&: c2)
    Just (sub,c1) -> return $ Just $ (sub,c1 :&: subst sub c2)
unifyOther _ _ = return Nothing             
             
envSearch c = do  
  binds <- getAnExist
  case binds of
    Nothing -> return Nothing
    Just (a,m) -> do
      cons <- rightSearch (var a) m
      return $ Just (mempty,cons)

unifyOne :: Constraint -> WithContext (Maybe (Substitution , Constraint))

unifyOne (a :=: b) = do
  c' <- isolateForFail $ unifyEq $ a :=: b 
  case c' of 
    Nothing -> isolateForFail $ unifyEq $ b :=: a
    r -> return r
unifyOne c = unifyOther unifyOne c


unifyEq cons@(a :=: b) = case (a,b) of 
  (Spine "#imp_forall#" [_, Abs a ty l], b) -> vtrace1 "-implicit-" $ do
    return $ Just (mempty, (∃) a ty $ l :=: b :&: var a :@: ty)
  (b, Spine "#imp_forall#" [_, Abs a ty l]) -> vtrace1 "-implicit-" $ do
    return $ Just (mempty,  (∃) a ty $ b :=: l :&: var a :@: ty)

  (Spine "#imp_abs#" (ty:l:r), b) -> vtrace1 ("-imp_abs- : "++show a ++ "\n\t"++show b) $ do
    a <- lift $ getNewWith "@a"
    return $ Just (mempty, (∃) a ty $ rebuildSpine l (var a:r) :=: b :&: var a :@: ty)
  (b, Spine "#imp_abs#" (ty:l:r)) -> vtrace1 "-imp_abs-" $ do
    a <- lift $ getNewWith "@a"
    return $ Just (mempty, (∃) a ty $ b :=: rebuildSpine l (var a:r):&: var a :@: ty)

  (Spine "#tycon#" [Spine nm [_]], Spine "#tycon#" [Spine nm' [_]]) | nm /= nm' -> throwError $ "different type constraints: "++show cons
  (Spine "#tycon#" [Spine nm [val]], Spine "#tycon#" [Spine nm' [val']]) | nm == nm' -> 
    return $ Just (mempty, val :=: val')
  (Spine "#tycon#" [Spine _ [val]], val') ->
    return $ Just (mempty, val :=: val')    
  (val', Spine "#tycon#" [Spine _ [val]]) ->
    return $ Just (mempty, val' :=: val)

  (Abs nm ty s , Abs nm' ty' s') -> vtrace1 "-aa-" $ do
    return $ Just (mempty, ty :=: ty' :&: ((∀) nm ty $ s :=: subst (nm' |-> var nm) s'))
  (Abs nm ty s , s') -> vtrace1 "-as-" $ do
    return $ Just (mempty, (∀) nm ty $  s :=: rebuildSpine s' [var nm])
    
  (s , s') | s == s' -> vtrace1 "-eq-" $ return $ Just (mempty, Top)
  (s@(Spine x yl), s') -> do
    bind <- getElm ("all: "++show cons) x
    case bind of
      Left bind@Binding{ elmQuant = Exists } -> do
        raiseToTop bind (Spine x yl) $ \(a@(Spine x yl),ty) sub ->
          case subst sub s' of
            b@(Spine x' y'l) -> do
              bind' <- getElm ("gvar-blah: "++show cons) x'
              case bind' of
                Right _ | S.member x $ freeVariables y'l -> 
                  vtrace1 ("CANT: -occ'- "++show (a :=: b)) $ 
                  throwError $ "occurs check: "++show (a :=: b)

                Right ty' -> vtrace1 "-gc- " $ vtrace2 (show cons) $ -- gvar-const
                  if allElementsAreVariables yl
                  then gvar_const (Spine x yl, ty) (Spine x' y'l, ty') 
                  else return Nothing
                Left Binding{ elmQuant = Forall } | not $ S.member x' $ freeVariables yl -> vtrace1 "CANT: -gu-dep-" $ throwError $ "gvar-uvar-depends: "++show (a :=: b)
                Left Binding{ elmQuant = Forall } | S.member x $ freeVariables y'l -> 
                  vtrace1 "CANT: -occ-" $ throwError $ "occurs check: "++show (a :=: b)
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
                         then vtrace1 "CANT: -ggd-occ-" $ throwError $ "occurs check: "++show (a :=: b)
                         else vtrace1 ("-ggd- " ++show cons)
                              $ gvar_gvar_diff (Spine x yl, ty) (Spine x' y'l, ty') bind
            _ -> vtrace1 "-ggs-" $ return Nothing
      _ -> case s' of 
        b@(Spine x' _) | x /= x' -> do
          bind' <- getElm ("const case: "++show cons) x'
          case bind' of
            Left Binding{ elmQuant = Exists } -> return Nothing
            _ -> vtrace1 ("CANT: -uud- two different universal equalities: "++show (a :=: b)) -- uvar-uvar 
                 $ throwError $ "two different universal equalities: "++show (a :=: b) -- uvar-uvar
        Spine x' yl' | x == x' -> vtrace1 ("-uue- ") $ vtrace3 (show (a :=: b)) $ do -- uvar-uvar-eq
          
          let match [] [] = return Top
              match ((Spine "#tycon#" [Spine nm [a]]):al) bl = case findTyconInPrefix nm bl of
                Nothing -> match al bl
                Just (b,bl) -> (a :=: b :&:) <$> match al bl
              -- in this case we know that al has no #tycon#s in its prefix since we exhausted all of them in the previous case
              match al (Spine "#tycon#" [Spine nm [v]]:bl) = match al bl 
              match (a:al) (b:bl) = (a :=: b :&:) <$>  match al bl
              match _ _ = throwError $ "different numbers of arguments on constant: "++show cons
                              
          cons <- match yl yl'
          return $ Just (mempty, cons)
        _ -> vtrace1 "CANT: -uvarpi-" $ throwError $ "uvar against a pi WITH CONS "++show cons
            
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
        let sub'' = sub *** sub'

        modify $ subst sub'
        return $ Just (sub'', cons)
  
  modify $ addToHead Exists x' ty' . removeFromContext x
  modify $ subst sub  
    
  -- now we can match against the right hand side
  r <- addSub =<< m (subst sub sp, ty') sub
  
  modify $ removeFromContext x'
  return r

      
getBase 0 a = a
getBase n (Spine "#forall#" [_, Abs _ _ r]) = getBase (n - 1) r
getBase _ a = a

-- TODO: make sure this is correct.  its now just a modification of gvar_gvar_diff!
gvar_gvar_same (Spine x yl, aty) (Spine _ y'l, _) = do
  let n = length yl
                    
      (uNl,atyl) = unzip $ take n $ typeToListOfTypes aty
      
  xN <- lift $ getNewWith "@ggs"
  
  let perm = [iyt | (iyt,_) <- filter (\(_,(a,b)) -> a == b) $ zip (zip uNl atyl) (zip yl y'l) ]
      
      makeBind us tyl arg = foldr (uncurry Abs) (Spine xN $ map var arg) $ zip us tyl
      
      l = makeBind uNl atyl $ map fst perm
      
      xNty = foldr (uncurry forall) (getBase n aty) perm
      
      sub = x |-> l
      
  modify $ addToTail Exists xN xNty -- THIS IS DIFFERENT FROM THE PAPER!!!!
  
  return $ Just (sub, Top)
  
gvar_gvar_same _ _ = error "gvar-gvar-same is not made for this case"

gvar_gvar_diff (a',aty') (sp, _) bind = raiseToTop bind sp $ \(b'@(Spine x' y'l), bty) subO -> do
  let (Spine x yl, aty) = (subst subO a', subst subO aty')
      
      -- now x' comes before x 
      -- but we no longer care since I tested it, and switching them twice reduces to original
  let n = length yl
      m = length y'l
                    
      (uNl,atyl) = unzip $ take n $ typeToListOfTypes aty
      (vNl,btyl) = unzip $ take m $ typeToListOfTypes bty
      
  xN <- lift $ getNewWith "@ggd"
  
  let perm = do
        (iyt,y) <- zip (zip uNl atyl) yl
        (i',_) <- filter (\(_,y') -> y == y') $ zip vNl y'l 
        return (iyt,i')
      
      makeBind us tyl arg = foldr (uncurry Abs) (Spine xN $ map var arg) $ zip us tyl
      
      l = makeBind uNl atyl $ map (fst . fst) perm
      l' = makeBind vNl btyl $ map snd perm
      
      xNty = foldr (uncurry forall) (getBase n aty) (map fst perm)
      
      sub = M.fromList [(x ,l), (x',l')]
  
  

  modify $ addToTail Exists xN xNty -- THIS IS DIFFERENT FROM THE PAPER!!!!
  return $ Just (sub, Top)
  
gvar_uvar_inside a@(Spine _ yl, _) b@(Spine y _, _) = 
  case elemIndex (var y) $ reverse yl of
    Nothing -> return Nothing
    Just _ -> gvar_uvar_outside a b
gvar_uvar_inside _ _ = error "gvar-uvar-inside is not made for this case"
  
gvar_const a@(Spine x yl, _) b@(Spine y _, bty) = case elemIndex (var y) $ yl of 
  Nothing -> gvar_fixed a b $ var . const y
  Just _ -> do 
{-    gvar_uvar_outside a b <|> gvar_fixed a b (var . const y) -}

    let ilst = [i | (i,y') <- zip [0..] yl , y' == var y] 
    defered <- lift $ getNewWith "@def"
    res <- gvar_fixed a b $ \ui_list -> 
      Spine defered $ var y:((ui_list !!) <$>ilst)
    modify $ addToHead Exists defered $ bty ~> foldr (\_ a -> bty ~> a) bty ilst
    return res

gvar_const _ _ = error "gvar-const is not made for this case"

gvar_uvar_outside a@(Spine x yl,_) b@(Spine y _,bty) = do
{-  let ilst = [i | (i,y') <- zip [0..] yl , y' == var y] 
  i <- F.asum $ return <$> ilst
  gvar_fixed a b $ (!! i)  -}

  case [i | (i,y') <- zip [0..] yl , y' == var y] of
    [i] -> vtrace1 ("-ic-") $ gvar_fixed a b lookup
      where lookup list = case length list <= i of
              True -> error $ show x ++ " "++show yl++"\n\tun: "++show list ++" \n\thas no " ++show i
              False -> list !! i
    ilst -> vtrace1 ("-il-") $ do
      defered <- lift $ getNewWith "@def"
      res <- gvar_fixed a b $ \ui_list -> 
        Spine defered $ (ui_list !!) <$> ilst
      modify $ addToHead Exists defered $ foldr (\_ a-> bty ~> a) bty ilst
      return res

gvar_uvar_outside _ _ = error "gvar-uvar-outside is not made for this case"

gvar_fixed (a@(Spine x _), aty) (b@(Spine _ y'l), bty) action = do
  let m = length y'l
      cons = a :=: b
  xm <- replicateM m $ lift $ getNewWith "@xm"
  
  let getArgs (Spine "#forall#" [ty, Abs ui _ r]) = ((var ui,ui),Left ty):getArgs r
      getArgs (Spine "#imp_forall#" [ty, Abs ui _ r]) = ((tycon ui $ var ui,ui),Right ty):getArgs r
      getArgs _ = []
      
      untylr = getArgs aty
      (un,_) = unzip untylr 
      (vun, _) = unzip un
      
      toLterm (Spine "#forall#" [ty, Abs ui _ r]) = Abs ui ty $ toLterm r
      toLterm (Spine "#imp_forall#" [ty, Abs ui _ r]) = imp_abs ui ty $ toLterm r      
      toLterm _ = rebuildSpine (action vun) $ (flip Spine vun) <$> xm
      
      l = toLterm aty
  
      vbuild e = foldr (\((_,nm),ty) a -> case ty of
                           Left ty -> forall nm ty a
                           Right ty -> imp_forall nm ty a
                       ) e untylr

      substBty sub (Spine "#forall#" [_, Abs vi bi r]) (xi:xmr) = (xi,vbuild $ subst sub bi)
                                                                :substBty (M.insert vi (Spine xi vun) sub) r xmr
      substBty sub (Spine "#imp_forall#" [_, Abs vi bi r]) (xi:xmr) = (xi,vbuild $ subst sub bi)
                                                                    : substBty (M.insert vi (Spine xi vun) sub) r xmr
      substBty _ _ [] = []
      substBty _ s l  = error $ "is not well typed: "++show s
                        ++"\nFOR "++show l 
                        ++ "\nON "++ show cons
      
      sub = x |-> l  -- THIS IS THAT STRANGE BUG WHERE WE CAN'T use x in the output substitution!
  
  modify $ flip (foldr ($)) $ uncurry (addToHead Exists) <$> substBty mempty bty xm  
  modify $ subst sub
  
  return $ Just (sub, subst sub $ a :=: b)

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
    return $ var y :=: rebuildSpine m [var x'] 
          :&: var y :@: b'

  Spine "#imp_forall#" [_, Abs x a b] -> do
    y <- lift $ getNewWith "@isY"
    x' <- lift $ getNewWith "@isX"
    let b' = subst (x |-> var x') b
    modify $ addToTail Forall x' a        
    modify $ addToTail Exists y b' 
    return $ var y :=: rebuildSpine m [tycon x $ var x']
          :&: var y :@: b'
    
  Spine nm _ -> do
    constants <- lift $ ask  
    foralls <- getForalls
    exists <- getExists        
    
    
    let envl = M.toList $ M.union (M.union foralls constants) exists
        
        sameFamily (_, Abs _ _ _) = False
        sameFamily ("pack",s) = "#exists#" == nm
        sameFamily (nm',s) = (M.notMember nm' exists || var nm' /= m) 
                             && getFamily s == nm
        targets = filter sameFamily envl
    case targets of
      [] -> vtrace3throw ("FAIL: "++nm++" @ "++show targets ++ " \n\t "++show exists)
      _ -> F.asum $ (leftSearch m goal <$> reverse targets) -- reversing works for now, but not forever!  need a heuristics + bidirectional search + control structures

vtrace3throw s = vtrace3 s $ throwError s

leftSearch m goal (x,target) = vtrace1 ("LS: " ++ show m ++" ∈ "++ show goal)
                             $ vtrace1 ("\t@ " ++x++" : " ++show target)
                             $ leftCont (var x) target
  where leftCont n target = fail ("No proof found:  "++show m ++" ∈ " ++show goal
                                 ++ "\n\t "++show x++" : "++show target) <|> case target of
          Spine "#forall#" [a, b] -> do
            x' <- lift $ getNewWith "@sla"
            modify $ addToTail Exists x' a
            cons <- leftCont (rebuildSpine n [var x']) (rebuildSpine b [var x'])
            return $ cons :&: var x' :@: a

          Spine "#imp_forall#" [_ , Abs x a b] -> do  
            x' <- lift $ getNewWith "@isla"
            modify $ addToTail Exists x' a
            cons <- leftCont (rebuildSpine n [tycon x $ var x']) (subst (x |-> var x') b)
            return $ cons :&: var x' :@: a
          Spine _ _ -> do
            return $ goal :=: target :&: m :=: n
          _ -> error $ "λ does not have type atom: " ++ show target

search :: Type -> WithContext (Substitution, Term)
search ty = do
  e <- lift $ getNewWith "@e"
  sub <- unify $ (∃) e ty $ var e :@: ty
  return $ (sub, subst sub $ var e)

-----------------------------
--- constraint generation ---
-----------------------------

(≐) a b = lift $ tell $ a :=: b
(.@.) a b = lift $ tell $ a :@: b

checkType :: Spine -> Type -> TypeChecker Spine
checkType sp ty = case sp of
  Spine "#ascribe#" (t:v:l) -> do
    v <- checkType v t
    checkType (rebuildSpine v l) ty
  
  Spine "#infer#" [_, Abs x tyA tyB ] -> do
    tyA <- checkType tyA atom
    x' <- getNewWith "@inf"
    addToEnv (∃) x' tyA $ do
      checkType (subst (x |-> var x') tyB) ty

  Spine "#imp_forall#" [_, Abs x tyA tyB] -> do
    tyA <- checkType tyA atom
    tyB <- addToEnv (∀) x tyA $ checkType tyB atom
    atom ≐ ty
    return $ imp_forall x tyA tyB
    
  Spine "#forall#" [_, Abs x tyA tyB] -> do
    tyA <- checkType tyA atom
    tyB <- addToEnv (∀) x tyA $ checkType tyB atom
    atom ≐ ty
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
        sp <- addToEnv (∀) x tyA $ checkType sp (Spine e [var x])
        return $ Abs x tyA sp

  Spine head args -> do
    let chop mty [] = do
          ty ≐ mty
          return []
          
        chop mty lst@(a:l) = case mty of 
          
          Spine "#imp_forall#" [ty', Abs nm _ tyv] -> case findTyconInPrefix nm lst of
            Nothing    -> do
              x <- getNewWith "@xin"
              addToEnv (∃) x ty' $ do
                chop (subst (nm |-> var x) tyv) lst
            Just (val,lst) -> do
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
      Nothing -> lift $ throwError $ "variable: "++show head++" not found in the environment."
      Just ty' -> Spine head <$> chop ty' args
              
test :: IO ()
test = case runError $ (\(a,_,_) -> a) <$> runRWST run (M.fromList consts) 0 of
  Left a -> putStrLn a
  Right sub -> putStrLn $ "success: "++show sub
  where run = do
          let constraint = (∀) "nat" atom
                         $ (∀) "z" (var "nat")
                         $ (∃) "v3" atom
                         $ (∃) "v5" (var "nat" ~> atom)
                         $ (Spine "v5" [var "z"]) :=: var "v3"

          runStateT (unify constraint) emptyContext

testGen :: Spine -> Type -> IO ()
testGen s t = do
  let Right ((ty,constraint),_,_) = runError $ runRWST (typeCheckToEnv $ checkType s t) envConsts 0
  putStrLn $ show ty
  putStrLn $ show constraint

----------------------
--- type inference ---
----------------------
typeInfer :: Constants -> (Name,Spine,Type) -> Choice Constants
typeInfer env (nm,val,ty) = (\r -> (\(a,_,_) -> a) <$> runRWST r (M.union envConsts env) 0) $ do

  (val,constraint) <- appendErr ("in name: "++ nm ++" : "++show val) $ 
                      trace ("Checking: " ++nm) $ 
                      vtrace0 ("\tVAL: " ++show val) $ 
                      vtrace0 ("\t:: " ++show ty) $ 
                      typeCheckToEnv $ checkType val ty
  (sub,ctxt) <- runStateT (unify constraint) emptyContext
  
  return $ M.insert nm (unsafeSubst sub val) env

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
          $ throwError $ "not the right family: need "++show fam++" for "++nm ++ " = " ++show val
        
        l' <- typeInfer l (nm,val,ty)
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
  Right (((s,tm),_),_,_) -> Right $ [("query", tm)]
  Left s -> Left $ "reification not possible: "++s
