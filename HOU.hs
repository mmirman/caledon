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
import Control.Monad.State (StateT, runStateT, modify, get, put)
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


-----------------------------------------------
---  the higher order unification algorithm ---
-----------------------------------------------

type WithContext = StateT Context Env 

type Unification = WithContext Substitution

getElm :: Name -> Name -> WithContext (Either Binding Spine)
getElm s x = do
  ty <- lookupConstant x
  case ty of
    Nothing -> Left <$> (\ctxt -> lookupWith ("looking up "++x++"\n\t in context: "++show ctxt++"\n\t"++s) x ctxt) <$> ctxtMap <$> get
    Just a -> return $ Right a

-- | This gets all the bindings outside of a given bind and returns them in a list (not including that binding).
getBindings :: Binding -> WithContext [(Name,Type)]
getBindings bind = do
  ctx <- get
  return $ snd <$> getBefore "IN: getBindings" bind ctx

getAllBindings = do
  ctx <- get
  getBindings $ getTail ctx
  
isolate m = do
  s <- get
  a <- m
  s' <- get
  put s
  return (s',a)

unify :: Constraint -> Unification
unify cons = do
  cons <- lift $ regenAbsVars cons

  let uniWhile c = do 
        res <- unifyOne c
        case res of
          Nothing -> return (mempty, c)
          Just (sub,c') -> do
            modify $ subst sub
            (\(s,c) -> (sub *** s, c)) <$> uniWhile c'
          
  fst <$> uniWhile cons
    
traceName = trace

isolateIf m = do
  (ns,c) <- isolate m
  case c of
    Just c -> do
      put ns
      return $ Just c
    Nothing -> return Nothing

unifyOne :: Constraint -> WithContext (Maybe (Substitution , Constraint))
unifyOne Top = return $ Nothing
unifyOne (Bind quant nm ty c) = do
  modify $ addToTail quant nm ty
  return $ Just (mempty, c)
unifyOne (c1 :&: c2) = do
  c1' <- unifyOne c1 
  case c1' of
    Nothing -> do 
      c2' <- unifyOne c2
      return $ case c2' of
        Nothing -> Nothing
        Just (sub,c2) -> Just $ (sub, subst sub c1 :&: c2)
    Just (sub,c1) -> return $ Just $ (sub,c1 :&: subst sub c2)
unifyOne (a :=: b) = do
  c' <- isolateIf $ unifyEq $ a :=: b 
  case c' of 
    Nothing -> isolateIf $ unifyEq $ b :=: a
    r -> return r

unifyEq cons@(a :=: b) = case (a,b) of 
  (Spine "#imp_forall#" [_, Abs a ty l], b) -> traceName "-implicit-" $ do
    return $ Just (mempty, (∃) a ty $ l :=: b)
  (b, Spine "#imp_forall#" [_, Abs a ty l]) -> traceName "-implicit-" $ do
    return $ Just (mempty,  (∃) a ty $ b :=: l)
    

  (Spine "#imp_abs#" (ty:l:r), b) -> traceName ("-imp_abs- : "++show a ++ "\n\t"++show b) $ do
    a <- lift $ getNewWith "@a"
    return $ Just (mempty, (∃) a ty $ rebuildSpine l (var a:r) :=: b)
  (b, Spine "#imp_abs#" (ty:l:r)) -> traceName "-imp_abs-" $ do
    a <- lift $ getNewWith "@a"
    return $ Just (mempty, (∃) a ty $ b :=: rebuildSpine l (var a:r))        
    
  (Abs nm ty s , Abs nm' ty' s') -> traceName "-aa-" $ do
    return $ Just (mempty, ty :=: ty' :&: ((∀) nm ty $ s :=: subst (nm' |-> var nm) s'))
  (Abs nm ty s , s') -> traceName "-as-" $ do
    return $ Just (mempty, (∀) nm ty $  s :=: rebuildSpine s' [var nm])
    
  (s , s') | s == s' -> traceName "-eq-" $ return $ Just (mempty, Top)
  (s@(Spine x yl), s') -> do
    bind <- getElm ("all: "++show cons) x
    case bind of
      Left bind@Binding{ elmQuant = Exists } -> do
        raiseToTop bind (Spine x yl) $ \(a@(Spine x yl),ty) sub ->
          case subst sub s' of
            Spine x' y'l -> do
              bind' <- getElm ("gvar-blah: "++show cons) x'
              case bind' of
                Right ty' -> traceName ("-gc- "++show cons) $ -- gvar-const
                  if allElementsAreVariables yl
                  then gvar_const (Spine x yl, ty) (Spine x' y'l, ty') 
                  else return Nothing
                Left Binding{ elmQuant = Forall } | not $ S.member x' $ freeVariables yl -> traceName "CANT: -gu-dep-" $ throwError $ "gvar-uvar-depends: "++show (a :=: b)
                Left Binding{ elmQuant = Forall } | S.member x $ freeVariables y'l -> 
                  traceName "CANT: -occ-" $ throwError $ "occurs check: "++show (a :=: b)
                Left Binding{ elmQuant = Forall, elmType = ty' } ->traceName "-gui-" $  -- gvar-uvar-inside
                  gvar_uvar_inside (Spine x yl, ty) (Spine x' y'l, ty')
                Left bind@Binding{ elmQuant = Exists, elmType = ty' } -> 
                  if not $ allElementsAreVariables yl && allElementsAreVariables y'l 
                  then return Nothing 
                  else if x == x' 
                       then traceName "-ggs-" $ -- gvar-gvar-same
                         gvar_gvar_same (Spine x yl, ty) (Spine x' y'l, ty')
                       else -- gvar-gvar-diff
                         if S.member x $ freeVariables y'l 
                         then traceName "CANT: -ggd-occ-" $ throwError $ "occurs check: "++show (a :=: b)
                         else traceName "-ggd-" $ gvar_gvar_diff (Spine x yl, ty) (Spine x' y'l, ty') bind
            _ -> traceName "-ggs-" $ return Nothing
      _ -> Just <$> case s' of 
        Spine x' _ | x /= x' -> do
          bind' <- getElm ("const case: "++show cons) x'
          case bind' of
            Left Binding{ elmQuant = Exists } -> traceName "-ug-" $ return $ (mempty,s' :=: s) -- uvar-gvar
            _ -> traceName ("CANT: -uud- two different universal equalities: "++show cons) -- uvar-uvar 
                 $ throwError $ "two different universal equalities: "++show cons -- uvar-uvar
        Spine x' yl' | x == x' -> traceName "-uue-" $ do -- uvar-uvar-eq
          unless (length yl == length yl') $ throwError $ "different numbers of arguments on constant: "++show cons
          return (mempty, foldl (:&:) Top $ zipWith (:=:) yl yl')
        _ -> traceName "CANT: -uvarpi-" $ throwError $ "uvar against a pi WITH CONS "++show cons
            
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
  let ilst = [i | (i,y') <- zip [0..] yl , y' == var y] 
  i <- F.asum $ return <$> ilst
  gvar_fixed a b $ var . (!! i)
  {-
  case [i | (i,y') <- zip [0..] yl , y' == var y] of
    [i] -> trace ("-ic-") $ gvar_fixed a b $ lookup
      where lookup list = case length list <= i of
              True -> error $ show x ++ " "++show yl++"\n\tun: "++show list ++" \n\thas no " ++show i
              False -> var $ list !! i
    ilst -> trace ("-il-") $ do
      defered <- lift $ getNewWith "@def"
      res <- gvar_fixed a b $ \ui_list -> 
        Spine defered $ var <$> (ui_list !!) <$> ilst
      modify $ addToHead Exists defered $ foldr (\_ a -> bty ~> a) bty ilst
      return res
  -}
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
-- AEEAEE
-- EEEEAA
--  (-> S)EEEAA 
--  (-> S)EEAA 

--------------------
--- proof search ---  
--------------------

getFamily (Spine "#infer#" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#ascribe#"  (_:v:l)) = getFamily v
getFamily (Spine "#forall#" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#imp_forall#" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#exists#" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#open#" (_:_:_:_:Abs _ _ (Abs _ _ c):_)) = getFamily c
getFamily (Spine nm' _) = nm'
getFamily v = error $ "values don't have families: "++show v

getEnv :: WithContext Constants
getEnv = do  
  nmMapA <- lift $ ask  
  nmMapB <- (fmap elmType . ctxtMap) <$> get
  return $ M.union nmMapB nmMapA 


search :: Type -> WithContext (Substitution, Term)
search goal = case goal of 
  Spine "#exists#" [_, Abs nm ty lm] -> do
    nm' <- lift $ getNewWith "@search"
    modify $ addToTail Exists nm' ty
    (sub, e) <- search $ subst (nm |-> var nm') lm 
    return $ (sub, pack e (subst sub $ var nm') nm ty lm)
    
  Spine "#forall#" [_, Abs nm ty lm] -> do
    nm' <- lift $ getNewWith "@sr"
    modify $ addToTail Forall nm' ty
    (sub,l) <- search $ subst (nm |-> var nm') lm
    modify $ removeFromContext nm'
    return (sub, Abs nm' (subst sub ty) l)
    
  Spine nm _ -> fail "" <|> do -- good time to do a breadth first search.
    -- here we ensure that since this might run infinitely deep without different cases, we stop somewhere along the way 
    -- to give other branches a fair shot at computation.
    env <- M.toList <$> getEnv
    let sameFamily s = getFamily s == nm
    F.asum $ left goal <$> filter (sameFamily . snd) env
    
  _ -> error $ "Not a type: "++show goal

left goal (x,target) = do
  let leftCont x target = case target of 
        Spine "#forall#" [_, Abs nm ty lm] -> do
          nm' <- lift $ getNewWith "@sla"
          -- by using existential quantification we can defer search implicitly
          modify $ addToTail Exists nm' ty
          (sub, result) <- leftCont x $ subst (nm |-> var nm') lm
          return $ (sub, \l -> result $ (subst sub $ var nm'):l )
          
        Spine "#exists#" [_, Abs nm ty lm] -> do 
          nm' <- lift $ getNewWith "@sle"
          -- universal quantification as information hiding
          modify $ addToTail Forall nm' ty
          (sub,result) <- leftCont x $ subst (nm |-> var nm') lm
          modify $ removeFromContext nm'
          
          p <- lift $ getNewWith "@p"
          return (sub, \l -> open (result []) (nm', ty) (p , subst (nm |-> var nm') lm) 
                             goal -- the goal never changes when we do left only substitution
                             $ Spine p l)

        Spine _ _ -> do
          -- should we really call a full unification here 
          -- and not just add the unification to the context 
          -- since unification is potentially incomplete & might defer? 
          -- we might want to include everything which can defer into one main loop.  
          sub <- unify $ goal :=: target 
          return (sub, \l -> Spine x l)
        _ -> error $ "λ does not have type atom: " ++ show target
  (sub,l) <- leftCont x target
  return (sub, subst sub $ l [])         
  
------------------------------------------
--- Constraint generation proof search ---
------------------------------------------
{-
this search works by adding constraints and variables to the prefix context, rather than 
simply "searching".  I'd need to compare and contrast merits with the entirely definite search.
-}
csearch :: Name -> Type -> WithContext Constraint
csearch m goal = case goal of           
  Spine "#forall#" [_, Abs x a b] -> do
    y <- lift $ getNewWith "@sY"
    modify $ addToTail Forall x a
    modify $ addToTail Exists y b
    cons <- csearch y b
    return $ cons :&: var y :=: rebuildSpine (var m) [var x]
  Spine nm _ -> do  
    env <- M.toList <$> getEnv
    let sameFamily s = getFamily s == nm
    F.asum $ cleft m goal <$> filter (sameFamily . snd) env
    
cleft m goal (x,target) = leftCont (var x) target
  where leftCont n target = case target of 
          Spine "#forall#" [_, Abs x a b] -> do
            nm' <- lift $ getNewWith "@sla"
            -- by using existential quantification we can defer search implicitly
            modify $ addToTail Exists x a
            cons1 <- leftCont (rebuildSpine n [var x]) b
            cons2 <- csearch x a
            return $ cons1 :&: cons2
          Spine _ _ -> do
            return $ goal :=: target :&: var m :=: var x
          _ -> error $ "λ does not have type atom: " ++ show target
    
-----------------------------
--- constraint generation ---
-----------------------------
(=.=) a b = lift $ tell $ a :=: b

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
    ty =.= exists imp tp interface
    return $ pack e tau imp tp interface

  Spine "#open#" [tp, Abs imp _ interface, closed, Abs _ _ (Abs _ _ c), Abs _ _ (Abs p _ exp)] -> do
    tp <- checkType tp atom
    closed <- checkType closed $ exists imp tp interface
    addToEnv (∀) imp tp $ do
      interface <- checkType interface atom
      addToEnv (∀) p interface $ do
        exp <- checkType exp ty    
        c <- checkType c atom
        c =.= ty
        return $ open closed (imp,tp) (p,interface) c exp
        
  Spine "#imp_forall#" [_, Abs x tyA tyB] -> do
    tyA <- checkType tyA atom
    tyB <- addToEnv (∀) x tyA $ checkType tyB atom
    atom =.= ty
    return $ imp_forall x tyA tyB
    
  Spine "#forall#" [_, Abs x tyA tyB] -> do
    tyA <- checkType tyA atom
    tyB <- addToEnv (∀) x tyA $ checkType tyB atom
    atom =.= ty
    return $ forall x tyA tyB

  Spine "#exists#" [_, Abs x tyA tyB] -> do
    tyA <- checkType tyA atom
    tyB <- addToEnv (∀) x tyA $ checkType tyB atom
    atom =.= ty
    return $ exists x tyA tyB
    
  -- below are the only cases where bidirectional type checking is useful 
  Spine "#imp_abs#" [_, Abs x tyA sp] -> case ty of
    Spine "#imp_forall#" [_, Abs x' tyA' tyF'] -> do
      tyA <- checkType tyA atom
      tyA =.= tyA'
      addToEnv (∀) x tyA $ do
        imp_abs x tyA <$> checkType sp (subst (x' |-> var x) tyF')
    _ -> do
      e <- getNewWith "@e"
      tyA <- checkType tyA atom
      addToEnv (∃) e (forall x tyA atom) $ do
        imp_forall x tyA (Spine e [var x]) =.= ty
        sp <- addToEnv (∀) x tyA $ checkType sp (Spine e [var x])
        return $ imp_abs x tyA sp

  Abs x tyA sp -> case ty of
    Spine "#forall#" [_, Abs x' tyA' tyF'] -> do
      tyA <- checkType tyA atom
      tyA =.= tyA'
      addToEnv (∀) x tyA $ do
        Abs x tyA <$> checkType sp (subst (x' |-> var x) tyF')
    _ -> do
      e <- getNewWith "@e"
      tyA <- checkType tyA atom
      addToEnv (∃) e (forall x tyA atom) $ do
        forall x tyA (Spine e [var x]) =.= ty
        sp <- addToEnv (∀) x tyA $ checkType sp (Spine e [var x])
        return $ Abs x tyA sp

  Spine head args -> do
    let chop mty [] = do
          ty =.= mty
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
              forall v (var x) (Spine tybody [var v]) =.= mty
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
  
  return $ M.insert nm (subst sub val) env
  

----------------------------
--- the public interface ---
----------------------------
typeCheckAxioms :: [(Maybe Name,Name,Spine,Type)] -> Choice Constants
typeCheckAxioms lst = do
  forM lst $ \(fam,_,val,_) -> case fam of
    Just fam -> unless (getFamily val == fam) $ throwError $ "not the right family: need "++show fam++" for "++show val
    Nothing -> return ()
  
  let toplst = topoSortAxioms $ map (\(_,a,b,t) -> (a,b,t)) lst
        
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
