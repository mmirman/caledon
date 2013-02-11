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
import Data.Monoid
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace

vtrace = const id

-----------------------------------------------
---  the higher order unification algorithm ---
-----------------------------------------------

unify :: Constraint -> WithContext Substitution
unify cons = do
  cons <- lift $ regenAbsVars cons
  let uniWhile c = uniWith unifyOne 
                 $ uniWith envSearch
                 $ checkFinished c >> return (mempty, c)
        where uniWith wth backup = do
                res <- wth c 
                case res of
                  Nothing -> backup
                  Just (sub, c') -> do
                    modify $ subst sub
                    (\(s,c) -> (sub *** s, c)) <$> uniWhile (reduceTops c')
  fst <$> uniWhile cons

reduceTops (a :=: b) = a :=: b
reduceTops Top = Top
reduceTops (c1 :&: c2) = case (reduceTops c1, reduceTops c2) of
  (Top,b) -> b
  (a,Top) -> a
  (a,b) -> a :&: b
reduceTops (Bind q nm ty b) = case reduceTops b of
  Top -> Top
  b -> Bind q nm ty b

checkFinished cval = do
  let cf c = case c of
          Top -> return ()
          Bind Forall _ _ c -> cf c
          c1 :&: c2 -> cf c1 >> cf c2
          _ -> throwError $ "ambiguous constraint: " ++show cval
  
  binds <- getExists
  unless (binds == Nothing) $ throwError $ "ambiguous constraint: " ++show cval
  cf cval
  
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
  binds <- getExists
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
  (Spine "#imp_forall#" [_, Abs a ty l], b) -> vtrace "-implicit-" $ do
    return $ Just (mempty, (∃) a ty $ l :=: b)
  (b, Spine "#imp_forall#" [_, Abs a ty l]) -> vtrace "-implicit-" $ do
    return $ Just (mempty,  (∃) a ty $ b :=: l)

  (Spine "#imp_abs#" (ty:l:r), b) -> vtrace ("-imp_abs- : "++show a ++ "\n\t"++show b) $ do
    a <- lift $ getNewWith "@a"
    return $ Just (mempty, (∃) a ty $ rebuildSpine l (var a:r) :=: b)
  (b, Spine "#imp_abs#" (ty:l:r)) -> vtrace "-imp_abs-" $ do
    a <- lift $ getNewWith "@a"
    return $ Just (mempty, (∃) a ty $ b :=: rebuildSpine l (var a:r))
    
  (Abs nm ty s , Abs nm' ty' s') -> vtrace "-aa-" $ do
    return $ Just (mempty, ty :=: ty' :&: ((∀) nm ty $ s :=: subst (nm' |-> var nm) s'))
  (Abs nm ty s , s') -> vtrace "-as-" $ do
    return $ Just (mempty, (∀) nm ty $  s :=: rebuildSpine s' [var nm])
    
  (s , s') | s == s' -> vtrace "-eq-" $ return $ Just (mempty, Top)
  (s@(Spine x yl), s') -> do
    bind <- getElm ("all: "++show cons) x
    case bind of
      Left bind@Binding{ elmQuant = Exists } -> do
        raiseToTop bind (Spine x yl) $ \(a@(Spine x yl),ty) sub ->
          case subst sub s' of
            Spine x' y'l -> do
              bind' <- getElm ("gvar-blah: "++show cons) x'
              case bind' of
                Right ty' -> vtrace ("-gc- "++show cons) $ -- gvar-const
                  if allElementsAreVariables yl
                  then gvar_const (Spine x yl, ty) (Spine x' y'l, ty') 
                  else return Nothing
                Left Binding{ elmQuant = Forall } | not $ S.member x' $ freeVariables yl -> vtrace "CANT: -gu-dep-" $ throwError $ "gvar-uvar-depends: "++show (a :=: b)
                Left Binding{ elmQuant = Forall } | S.member x $ freeVariables y'l -> 
                  vtrace "CANT: -occ-" $ throwError $ "occurs check: "++show (a :=: b)
                Left Binding{ elmQuant = Forall, elmType = ty' } ->vtrace "-gui-" $  -- gvar-uvar-inside
                  gvar_uvar_inside (Spine x yl, ty) (Spine x' y'l, ty')
                Left bind@Binding{ elmQuant = Exists, elmType = ty' } -> 
                  if not $ allElementsAreVariables yl && allElementsAreVariables y'l 
                  then return Nothing 
                  else if x == x' 
                       then vtrace "-ggs-" $ -- gvar-gvar-same
                         gvar_gvar_same (Spine x yl, ty) (Spine x' y'l, ty')
                       else -- gvar-gvar-diff
                         if S.member x $ freeVariables y'l 
                         then vtrace "CANT: -ggd-occ-" $ throwError $ "occurs check: "++show (a :=: b)
                         else vtrace "-ggd-" $ gvar_gvar_diff (Spine x yl, ty) (Spine x' y'l, ty') bind
            _ -> vtrace "-ggs-" $ return Nothing
      _ -> Just <$> case s' of 
        Spine x' _ | x /= x' -> do
          bind' <- getElm ("const case: "++show cons) x'
          case bind' of
            Left Binding{ elmQuant = Exists } -> vtrace "-ug-" $ return $ (mempty,s' :=: s) -- uvar-gvar
            _ -> vtrace ("CANT: -uud- two different universal equalities: "++show cons) -- uvar-uvar 
                 $ throwError $ "two different universal equalities: "++show cons -- uvar-uvar
        Spine x' yl' | x == x' -> vtrace "-uue-" $ do -- uvar-uvar-eq
          unless (length yl == length yl') $ throwError $ "different numbers of arguments on constant: "++show cons
          return (mempty, foldl (:&:) Top $ zipWith (:=:) yl yl')
        _ -> vtrace "CANT: -uvarpi-" $ throwError $ "uvar against a pi WITH CONS "++show cons
            
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
      
  xN <- lift $ getNewWith "@x'"
  
  let perm = [iyt | (iyt,_) <- filter (\(_,(a,b)) -> a == b) $ zip (zip uNl atyl) (zip yl y'l) ]
      
      makeBind us tyl arg = foldr (uncurry Abs) (Spine xN $ map var arg) $ zip us tyl
      
      l = makeBind uNl atyl $ map fst perm
      
      xNty = foldr (uncurry forall) (getBase n aty) perm
      
      sub = x |-> l
      
  modify $ addToHead Exists xN xNty
  
  return $ Just (sub, Top)
  
gvar_gvar_same _ _ = error "gvar-gvar-same is not made for this case"

gvar_gvar_diff (a',aty') (sp, _) bind = raiseToTop bind sp $ \(Spine x' y'l, bty) subO -> do
  let (Spine x yl, aty) = (subst subO a', subst subO aty')
      
      -- now x' comes before x 
      -- but we no longer care since I tested it, and switching them twice reduces to original
  let n = length yl
      m = length y'l
                    
      (uNl,atyl) = unzip $ take n $ typeToListOfTypes aty
      (vNl,btyl) = unzip $ take m $ typeToListOfTypes bty
      
  xN <- lift $ getNewWith "@x'"
  
  let perm = do
        (iyt,y) <- zip (zip uNl atyl) yl
        (i',_) <- filter (\(_,y') -> y == y') $ zip vNl y'l 
        return (iyt,i')
      
      makeBind us tyl arg = foldr (uncurry Abs) (Spine xN $ map var arg) $ zip us tyl
      
      l = makeBind uNl atyl $ map (fst . fst) perm
      l' = makeBind vNl btyl $ map snd perm
      
      xNty = foldr (uncurry forall) (getBase n aty) (map fst perm)
      
      sub = M.fromList [(x ,l), (x',l')]
      
  modify $ addToHead Exists xN xNty
  
  return $ Just (sub,Top)
  
gvar_uvar_inside a@(Spine _ yl, _) b@(Spine y _, _) = 
  case elemIndex (var y) $ reverse yl of
    Nothing -> return Nothing
    Just _ -> gvar_uvar_outside a b
gvar_uvar_inside _ _ = error "gvar-uvar-inside is not made for this case"
  
gvar_const a@(Spine _ yl, _) b@(Spine y _, _) = case elemIndex (var y) $ yl of 
  Nothing -> gvar_fixed a b $ var . const y
  Just _ -> gvar_uvar_outside a b <|> gvar_fixed a b (var . const y)
gvar_const _ _ = error "gvar-const is not made for this case"


gvar_uvar_outside a@(Spine x yl,_) b@(Spine y _,bty) = do
{-  let ilst = [i | (i,y') <- zip [0..] yl , y' == var y] 
  i <- F.asum $ return <$> ilst
  gvar_fixed a b $ var . (!! i)
-}
  case [i | (i,y') <- zip [0..] yl , y' == var y] of
    [i] -> vtrace ("-ic-") $ gvar_fixed a b $ lookup
      where lookup list = case length list <= i of
              True -> error $ show x ++ " "++show yl++"\n\tun: "++show list ++" \n\thas no " ++show i
              False -> var $ list !! i
    ilst -> vtrace ("-il-") $ do
      defered <- lift $ getNewWith "@def"
      res <- gvar_fixed a b $ \ui_list -> 
        Spine defered $ var <$> (ui_list !!) <$> ilst
      modify $ addToHead Exists defered $ foldr (\_ a -> bty ~> a) bty ilst
      return res

gvar_uvar_outside _ _ = error "gvar-uvar-outside is not made for this case"

gvar_fixed (a@(Spine x _), aty) (b@(Spine _ y'l), bty) action = do
  let m = length y'l
  xm <- replicateM m $ lift $ getNewWith "@xm"
  
  let getArgs (Spine "#forall#" [ty, Abs ui _ r]) = (ui,ty):getArgs r
      getArgs _ = []
      
      untylr = getArgs aty
      (un,_) = unzip untylr 
      
      vun = var <$> un
      
      toLterm (Spine "#forall#" [ty, Abs ui _ r]) = Abs ui ty $ toLterm r
      toLterm _ = rebuildSpine (action un) $ (flip Spine vun) <$> xm
      
      l = toLterm aty
  
      vbuild e = foldr (\(nm,ty) a -> forall nm ty a) e untylr

      substBty sub (Spine "#forall#" [_, Abs vi bi r]) (xi:xmr) = (xi,vbuild $ subst sub bi)
                                                                :substBty (M.insert vi (Spine xi vun) sub) r xmr
      substBty _ _ [] = []
      substBty _ _ _  = error $ "s is not well typed"
      
      sub = x |-> l  -- THIS IS THAT STRANGE BUG WHERE WE CAN'T use x in the output substitution!
  
  modify $ flip (foldr ($)) $ uncurry (addToHead Exists) <$> substBty mempty bty xm  
  modify $ subst sub
  
  return $ Just (sub, subst sub $ a :=: b)

gvar_fixed _ _ _ = error "gvar-fixed is not made for this case"

--------------------
--- proof search ---  
--------------------
getEnv :: WithContext Constants
getEnv = do  
  nmMapA <- lift $ ask  
  nmMapB <- (fmap elmType . ctxtMap) <$> get
  return $ M.union nmMapB nmMapA 

-- need bidirectional search!
rightSearch :: Term -> Type -> WithContext Constraint
rightSearch m goal = vtrace ("-rs- "++show m++" ∈ "++show goal) $ case goal of
  Spine "#forall#" [_, Abs x a b] -> do
    y <- lift $ getNewWith "@sY"
    x' <- lift $ getNewWith "@sX"
    modify $ addToTail Forall x' a
    let b' = subst (x |-> var x') b
    modify $ addToTail Exists y b'
    cons <- rightSearch (var y) b'
    return $ var y :=: rebuildSpine m [var x'] :&: cons

  Spine "#imp_forall#" [_, Abs x a b] -> do
    y <- lift $ getNewWith "@isY"
    x' <- lift $ getNewWith "@isX"
    modify $ addToTail Forall x' a
    let b' = subst (x |-> var x') b
    modify $ addToTail Exists y b'
    cons <- rightSearch (var y) b'
    return $ var y :=: rebuildSpine m [tycon x $ var x'] :&: cons

  Spine nm _ -> do
    env <- getEnv
    let envl = M.toList env
        sameFamily (Abs _ _ _) = False
        sameFamily s = getFamily s == nm
    case m of 
      Spine nm _ | M.member nm env -> do
        leftSearch m goal (nm, env M.! nm)
      _ -> F.asum $ leftSearch m goal <$> filter (sameFamily . snd) envl

leftSearch m goal (x,target) = vtrace "-ls-" $ leftCont (var x) target
  where leftCont n target = fail ("No proof found:  "++show m ++" ∈ " ++show goal) <|> case target of
          
          Spine "#forall#" [_, Abs x a b] -> do
            x' <- lift $ getNewWith "@sla"
            modify $ addToTail Exists x' a
            cons1 <- leftCont (rebuildSpine n [var x']) (subst (x |-> var x') b)
            cons2 <- rightSearch (var x') a
            return $ cons1 :&: cons2
            
          Spine "#imp_forall#" [_ , Abs x a b] -> do  
            x' <- lift $ getNewWith "@isla"
            modify $ addToTail Exists x' a
            cons1 <- leftCont (rebuildSpine n [tycon x $ var x']) (subst (x |-> var x') b)
            cons2 <- rightSearch (var x') a
            return $ cons1 :&: cons2

          Spine _ _ -> do
            return $ goal :=: target :&: m :=: n
          _ -> error $ "λ does not have type atom: " ++ show target

search :: Type -> WithContext (Substitution, Term)
search ty = do
  e <- lift $ getNewWith "e"
  sub <- unify $ (∃) e ty $ Top
  return $ (sub, subst sub $ var e)

-----------------------------
--- constraint generation ---
-----------------------------

(≐) a b = lift $ tell $ a :=: b

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

  Spine "#pack#" [tp, Abs imp _ interface, tau, e] -> do
    tp <- checkType tp atom    
    tau <- checkType tau tp
    interface <- addToEnv (∀) imp tp $ checkType interface atom
    e <- checkType e (subst (imp |-> tau) interface)    
    ty ≐ exists imp tp interface
    return $ pack e tau imp tp interface

  Spine "#open#" [tp, Abs imp _ interface, closed, Abs _ _ (Abs _ _ c), Abs _ _ (Abs p _ exp)] -> do
    tp <- checkType tp atom
    closed <- checkType closed $ exists imp tp interface
    addToEnv (∀) imp tp $ do
      interface <- checkType interface atom
      addToEnv (∀) p interface $ do
        exp <- checkType exp ty    
        c <- checkType c atom
        c ≐ ty
        return $ open closed (imp,tp) (p,interface) c exp
        
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

  Spine "#exists#" [_, Abs x tyA tyB] -> do
    tyA <- checkType tyA atom
    tyB <- addToEnv (∀) x tyA $ checkType tyB atom
    atom ≐ ty
    return $ exists x tyA tyB
    
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
          
        chop mty (a:l) = case mty of 
          Spine "#imp_forall#" [ty', Abs nm _ tyv] -> case a of
            Spine "#tycon#" [Spine nm' [val]] | nm' == nm -> do
              val <- checkType val ty'
              chop (subst (nm |-> val) tyv) l              
            _ -> do
              x <- getNewWith "@xin"
              addToEnv (∃) x ty' $ 
                chop (subst (nm |-> var x) tyv) (a:l)
                
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
                      trace ("Checking: " ++nm) $ typeCheckToEnv $ checkType val ty
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
  forM lst $ \(fam,_,val,_) -> case fam of
    Just fam -> unless (getFamily val == fam) $ throwError $ "not the right family: need "++show fam++" for "++show val
    Nothing -> return ()
  
  let toplst = topoSortAxioms $ map (\(fam,a,b,t) -> (a,b,t)) lst
        
  F.foldlM typeInfer mempty toplst

typeCheckAll :: [Predicate] -> Choice [Predicate]
typeCheckAll preds = do
  let toAxioms (Predicate nm ty cs) = (Just "atom",nm,ty,atom):map (\(nm',ty') -> (Just nm,nm',ty',atom)) cs
      toAxioms (Query nm val) = [(Nothing, nm,val,atom)]
      toAxioms (Define nm val ty) = [(Just $ getFamily ty, nm,ty,atom), (Nothing, "#val: "++nm,val,ty)]
  tyMap <- typeCheckAxioms (concatMap toAxioms preds)
  
  let newPreds (Predicate nm _ cs) = Predicate nm (tyMap M.! nm) $ map (\(nm,_) -> (nm,tyMap M.! nm)) cs
      newPreds (Query nm _) = Query nm (tyMap M.! nm)
      newPreds (Define nm _ _) = Define nm (tyMap M.! ("#val: "++nm)) (tyMap M.! nm)
  
  return $ newPreds <$> preds
  
solver :: [(Name,Type)] -> Type -> Either String [(Name, Term)]
solver axioms tp = case runError $ runRWST (runStateT (search tp) emptyContext) (M.union envConsts $ M.fromList axioms) 0 of
  Right (((s,tm),_),_,_) -> Right $ ("query", tm):(map (\a -> (a,var a)) $ S.toList $ freeVariables tp)
  Left s -> Left $ "reification not possible: "++s
