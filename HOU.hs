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
import Control.Monad.State (StateT, runStateT, modify, get, put)
import Control.Monad.RWS (RWST, runRWST, ask)
import Control.Monad.Error (throwError, MonadError)
import Control.Monad (unless, forM, replicateM)
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
  
flatten :: Constraint -> ([(Quant, Name, Type)], [(Spine, Spine)])
flatten cons = case cons of
  Top -> ([],[])
  c1 :&: c2 -> let (binds1,c1') = flatten c1
                   (binds2,c2') = flatten c2
               in  (binds1++binds2,c1'++c2')
  Bind quant nm ty c -> ((quant,nm,ty):binds,c')
    where (binds, c') = flatten c
  a :=: b -> ([],[(a,b)])
  
addBinds :: [(Quant, Name, Type)] -> WithContext ()
addBinds binds = mapM_ (\(quant,nm,ty) -> modify $ addToTail quant nm ty) binds   


isolate m = do
  s <- get
  a <- m
  s' <- get
  put s
  return (s',a)
  
unify :: Constraint -> Unification
unify cons = do
  cons <- lift $ regenAbsVars cons
  let (binds,constraints) = trace (show cons) $ flatten cons
  addBinds binds      
  let with l r newstate sub cons = do
        let (binds,constraints) = flatten cons
            
        put newstate
        addBinds binds
        let l' = subst sub <$> l
            r' = subst sub <$> reverse r
            res = (sub,l'++constraints++r')
            
        return res
      uniOne [] _  = throwError "can not unify any further"
      uniOne ((a,b):l) r = do
        (newstate,choice) <- isolate $ unifyEq a b
        case choice of
          Just (sub,cons) -> with l r newstate sub cons
          Nothing -> do 
            (newstate,choice) <- isolate $ unifyEq b a 
            case choice of
              Just (sub, cons) -> with l r newstate sub cons
              Nothing -> uniOne l ((a,b):r)
     
      uniWhile [] = return mempty
      uniWhile l = do 
        (sub,l') <- uniOne l []
          
        modify $ subst sub
        (sub ***) <$> uniWhile l'
      
  uniWhile constraints

traceName _ = id

unifyEq :: Spine -> Spine -> WithContext (Maybe (Substitution , Constraint))
unifyEq a b = let cons = a :=: b in case (a,b) of 
  (Abs nm ty s , Abs nm' ty' s') -> traceName "-aa-" $ do
    return $ Just (mempty, ty :=: ty' :&: (Bind Forall nm ty $ s :=: subst (nm' |-> var nm) s'))
  (Abs nm ty s , s') -> traceName "-as-" $ do
    return $ Just (mempty, Bind Forall nm ty $  s :=: rebuildSpine s' [var nm])
  (s , s') | s == s' -> traceName "-eq-" $ return $ Just (mempty, Top)
  (s@(Spine x yl), s') -> do
    bind <- getElm ("all: "++show cons) x
    case bind of
      Left bind@Binding{ elmQuant = Exists } -> do
        raiseToTop bind (Spine x yl) $ \(a@(Spine x yl),ty) sub ->
          case subst sub s' of
            Spine x' y'l -> do
              bind' <- getElm "gvar-blah" x'
              case bind' of
                Right ty' -> traceName "-gc-" $ -- gvar-const
                  gvar_const (Spine x yl, ty) (Spine x' y'l, ty') 
                Left Binding{ elmQuant = Forall } | not $ S.member x' $ freeVariables yl -> traceName "-gu-dep-" $ throwError $ "gvar-uvar-depends: "++show (a :=: b)
                Left Binding{ elmQuant = Forall } | S.member x $ freeVariables yl -> traceName "-occ-" $ throwError $ "occurs check: "++show (a :=: b)
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
                         then traceName "-ggd-occ-" $ throwError $ "occurs check: "++show (a :=: b)
                         else traceName "-ggd-" $ gvar_gvar_diff (Spine x yl, ty) (Spine x' y'l, ty') bind
            _ -> traceName "-ggs-" $ return Nothing
      _ -> Just <$> case s' of 
        Spine x' _ | x /= x' -> do
          bind' <- getElm ("const case: "++show cons) x'
          case bind' of
            Left Binding{ elmQuant = Exists } -> traceName "-ug-" $ return $ (mempty,s' :=: s) -- uvar-gvar
            _ -> traceName "-uud-" $ throwError $ "two different universal equalities: "++show cons -- uvar-uvar
        Spine x' yl' | x == x' -> traceName "-uue-" $ do -- uvar-uvar-eq
          unless (length yl == length yl') $ throwError $ "different numbers of arguments on constant: "++show cons
          return (mempty, foldl (:&:) Top $ zipWith (:=:) yl yl')
        _ -> throwError $ "uvar against a pi WITH CONS "++show cons
            
allElementsAreVariables :: [Spine] -> Bool
allElementsAreVariables = all $ \c -> case c of
  Spine _ [] -> True
  _ -> False

typeToListOfTypes (Spine _ _) = []
typeToListOfTypes (Abs x ty l) = (x,ty):typeToListOfTypes l

-- the problem WAS (hopefully) here that the binds were getting
-- a different number of substitutions than the constraints were.
-- make sure to check that this is right in the future.
raiseToTop bind@Binding{ elmName = x, elmType = ty } sp m = do
  hl <- reverse <$> getBindings bind
  
  let newx_args = map (var . fst) hl
      sub = x |-> Spine x newx_args
      
      ty' = foldr (\(nm,ty) a -> forall nm ty a) ty hl
        
      addSub Nothing = return $ Nothing
      addSub (Just (sub',cons)) = do
        let sub'' = case M.lookup x sub' of
              Nothing -> sub *** sub'
              Just xv -> sub' *** (x |-> rebuildSpine xv newx_args)
        modify $ subst sub'                
        return $ Just (sub'', subst sub'' cons)
  
  modify $ removeFromContext x
  modify $ subst sub  
  
    
  -- now we can match against the right hand side
  addSub =<< m (subst sub sp, ty') sub


      
getBase 0 a = a
getBase n (Spine "forall" [_, Abs _ _ r]) = getBase (n - 1) r
getBase _ a = a

-- TODO: make sure this is correct.  its now just a modification of gvar_gvar_diff!
gvar_gvar_same (a@(Spine x yl), aty) (b@(Spine _ y'l), _) = do
  let n = length yl
                    
      (uNl,atyl) = unzip $ take n $ typeToListOfTypes aty
      
  xN <- lift $ getNewWith "@x'"
  
  let perm = [iyt | (iyt,_) <- filter (\(_,(a,b)) -> a == b) $ zip (zip uNl atyl) (zip yl y'l) ]
      
      makeBind us tyl arg = foldr (uncurry Abs) (Spine xN $ map var arg) $ zip us tyl
      
      l = makeBind uNl atyl $ map fst perm

      
      xNty = foldr (uncurry forall) (getBase n aty) perm
      
      sub = x |-> l
      
  modify $ addToHead Exists xN xNty
  return $ Just (sub, subst sub $ a :=: b)
gvar_gvar_same _ _ = error "gvar-gvar-same is not made for this case"

gvar_gvar_diff (a',aty') (sp, _) bind = raiseToTop bind sp $ \(sp@(Spine x' y'l), bty) subO -> do
  let (a@(Spine x yl), aty) = (subst subO a', subst subO aty')
      
  -- now x' comes before x 
  -- but we no longer care since I tested it, and switching them twice reduces to original
  let n = length yl
      m = length y'l
                    
      (uNl,atyl) = unzip $ take n $ typeToListOfTypes aty
      (vNl,btyl) = unzip $ take m $ typeToListOfTypes bty
      
  xN <- lift $ getNewWith "@x'"
  
  let perm = [(iyt,i') | (iyt,y) <- zip (zip uNl atyl) yl, (i',_) <- filter (\(_,y') -> y == y') $ zip vNl y'l ]
      
      makeBind us tyl arg = foldr (uncurry Abs) (Spine xN $ map var arg) $ zip us tyl
      
      l = makeBind uNl atyl $ map (fst . fst) perm
      l' = makeBind vNl btyl $ map snd perm
      
      xNty = foldr (uncurry forall) (getBase n aty) (map fst perm)
      
      sub = (x |-> l) *** (x' |-> l')
      
  modify $ addToHead Exists xN xNty
  return $ Just (sub, subst sub $ a :=: sp)
  
gvar_uvar_inside a@(Spine _ yl, _) b@(Spine y _, _) = 
  case elemIndex (var y) $ reverse yl of
    Nothing -> return Nothing
    Just _ -> gvar_uvar_outside a b
gvar_uvar_inside _ _ = error "gvar-uvar-inside is not made for this case"
  
gvar_const a@(Spine _ yl, _) b@(Spine y _, _) = case elemIndex (var y) $ yl of 
  Nothing -> gvar_fixed a b $ var . const y
  Just _ -> gvar_fixed a b (var . const y) <|> gvar_uvar_outside a b
gvar_const _ _ = error "gvar-const is not made for this case"

gvar_uvar_outside a@(Spine _ yl,_) b@(Spine y _,_) = do
  let ilst = [i | (i,y') <- zip [0..] yl , y' == var y] 
  i <- F.asum $ return <$> ilst
  gvar_fixed a b $ var . (!! i)
gvar_uvar_outside _ _ = error "gvar-uvar-outside is not made for this case"

gvar_fixed (a@(Spine x _), aty) (b@(Spine _ y'l), bty) action = do
  let m = length y'l
  xm <- replicateM m $ lift $ getNewWith "@xm"
  
  let getArgs (Spine "forall" [ty, Abs ui _ r]) = (ui,ty):getArgs r
      getArgs _ = []
      
      untylr = getArgs aty
      (un,_) = unzip untylr 
      
      vun = var <$> un
      
      toLterm (Spine "forall" [ty, Abs ui _ r]) = Abs ui ty $ toLterm r
      toLterm _ = rebuildSpine (action un) $ (flip Spine vun) <$> xm
      
      l = toLterm aty
  
      vbuild e = foldr (\(nm,ty) a -> forall nm ty a) e untylr

      substBty sub (Spine "forall" [_, Abs vi bi r]) (xi:xmr) = (xi,vbuild $ subst sub bi)
                                                                :substBty (M.insert vi (Spine xi vun) sub) r xmr
      substBty _ _ [] = []
      substBty _ _ _  = error $ "s is not well typed"
      
      sub = x |-> l  -- THIS IS THAT STRANGE BUG WHERE WE CAN'T use x in the output substitution!
  
  modify $ flip (foldr ($)) $ uncurry (addToHead Exists) <$> substBty mempty bty xm  
  return $ Just (sub, subst sub $ a :=: b)

gvar_fixed _ _ _ = error "gvar-fixed is not made for this case"

--------------------
--- proof search ---  
--------------------

getFamily (Spine "forall" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#open#" (_:_:c:_)) = getFamily c
getFamily (Spine nm' _) = nm'
getFamily v = error $ "values don't have families: "++show v
                      

getEnv :: WithContext Constants
getEnv = do  
  nmMapA <- lift $ ask  
  nmMapB <- (fmap elmType . ctxtMap) <$> get
  return $ M.union nmMapB nmMapA 
  
search :: Type -> WithContext (Substitution, Term)
search goal = case goal of 
  Spine "exists" [Abs nm ty lm] -> do
    
    -- this case is a bit strange as we rely on unification, either now
    -- OR in the FUTURE in order to find the actual value for tau/nm'
    -- so we can't delete nm' from the context.
    
    nm' <- lift $ getNewWith "@search"
    modify $ addToTail Exists nm' ty
    
    (sub, e) <- search $ subst (nm |-> var nm') lm 
    return $ (sub, pack e (subst sub $ var nm') nm ty lm)
    
  Spine "forall" [_, Abs nm ty lm] -> do
    nm' <- lift $ getNewWith "@sr"
    modify $ addToTail Forall nm' ty
    (sub,l) <- search $ subst (nm |-> var nm') lm
    modify $ removeFromContext nm'
    return (sub, Abs nm' (subst sub ty) l)
  Spine nm _ -> fail "" <|> do 
    -- here we ensure that since this might run infinitely deep without different cases, we stop somewhere along the way 
    -- to give other branches a fair shot at computation.
    env <- M.toList <$> getEnv
    let sameFamily s = getFamily s == nm
    F.asum $ left goal <$> filter (sameFamily . snd) env
    
  _ -> error $ "Not a type: "++show goal
  
left goal (x,target) = do
  let leftCont x target = case target of 
        Spine "forall" [_, Abs nm ty lm] -> do
          nm' <- lift $ getNewWith "@sla"
          -- by using existential quantification we can defer search implicitly
          modify $ addToTail Exists nm' ty
          (sub, result)  <- leftCont x $ subst (nm |-> var nm') lm
          return $ (sub, \l -> result $ (subst sub $ var nm'):l )
            
        Spine "exists" [_, Abs nm ty lm] -> do 
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
          sub <- unify $ goal :=: target
          return (sub, \l -> Spine x l)
        _ -> error $ "λ does not have type atom: " ++ show target
  (sub,l) <- leftCont x target
  return (sub, subst sub $ l [])         

          
-----------------------------
--- constraint generation ---
-----------------------------
checkType :: Spine -> Type -> Env Constraint
checkType sp ty = case sp of
  Abs x tyA sp -> do
    e <- getNewWith "@e"
    cons1 <- checkType ty atom
    cons2 <- addToEnv (∃) e (forall x tyA atom) $ do
      cons2 <- addToEnv (∀) x tyA $ checkType sp (Spine e [var x])
      return $ cons2 :&: forall x tyA (Spine e [var x]) :=: ty
    return $ cons1 :&: cons2
      
  Spine "#pack#" [tp, Abs imp _ interface, tau, e] -> do
    cons1 <- checkType tp atom    
    cons2 <- checkType tau tp
    cons3 <- addToEnv (∀) imp tp $ checkType interface atom
    cons4 <- checkType e (subst (imp |-> tau) interface)
    return $ cons1 
         :&: cons2 
         :&: cons3 
         :&: cons4
         :&: ty :=: exists imp tp interface
  Spine "#open#" [tp, Abs imp _ interface, closed, Abs _ _ (Abs _ _ c), Abs _ _ (Abs p _ exp)] -> do
    cons1 <- checkType tp atom
    cons2 <- checkType closed $ exists imp tp interface
    cons3 <- addToEnv (∀) imp tp $ do
      cons1 <- checkType interface atom
      cons2 <- addToEnv (∀) p interface $ do
        cons1 <- checkType exp ty    
        let cip = rebuildSpine c [var imp, var p]
        cons2 <- checkType cip atom
        return $ cons1 :&: cons2 :&: (cip :=: ty)
      return $ cons1 :&: cons2
    return $ cons1 :&: cons2 :&: cons3 
    
  Spine "forall" [_, Abs x tyA tyB] -> do
    cons1 <- checkType tyA atom
    cons2 <- addToEnv (∀) x tyA $ checkType tyB atom
    return $ atom :=: ty :&: cons1 :&: cons2
  Spine "exists" [_, Abs x tyA tyB] -> do
    cons1 <- checkType tyA atom
    cons2 <- addToEnv (∃) x tyA $ checkType tyB atom
    return $ atom :=: ty :&: cons1 :&: cons2    
  Spine head args -> cty (head, reverse args) ty
    where cty (head,[]) ty = do
            mty <- (M.lookup head) <$> ask
            case mty of
              Nothing  -> throwError $ "variable: "++show head++" not found in the environment."
              Just ty' -> do
                return $ ty' :=: ty
          cty (head,arg:rest) tyB = do
            x <- getNewWith "@xin"
            tyB' <- getNewWith "@tyB'"
            tyA  <- getNewWith "@tyA"
            let tyB'ty = forall x (var tyA) atom
            addToEnv (∃) tyA atom $ addToEnv (∃) tyB' tyB'ty $ do
              let cons1 = Spine tyB' [arg] :=: tyB
              cons2 <- cty (head,rest) $ forall x (var tyA) $ Spine tyB' [var x]
              cons3 <- checkType arg $ var tyA
              return $ cons1 :&: cons2 :&: cons3

{-
open :: ∀ T : atom . 
        ∀ Af : T -> atom .
        ∀ cls : (∃ x : T . Af x) . 
        ∀ CtF : (∀ x : T . ∀ p : Af x . atom) .
        ∀ out : (∀ x : T . ∀ p : Af x . CtF x p) . 
        open T Af cls (\x:T.\p:Af x. atom) (\x:T.\p:Af x.CtF)
-}

consts = [ ("atom", atom)
         , ("forall", forall "a" atom $ (var "a" ~> atom) ~> atom)
         , ("exists", forall "a" atom $ (var "a" ~> atom) ~> atom)
         , ("#pack#", forall "tp" atom 
                    $ forall "iface" (var "tp" ~> atom) 
                    $ forall "tau" (var "tp") 
                    $ forall "e" (Spine "iface" [var "tau"]) 
                    $ exists "imp" (var "tp") (Spine "iface" [var "imp"]))
         , ("#open#", forall "tp" atom 
                    $ forall "iface" (var "tp" ~> atom) 
                    $ forall "closed" (exists "imp" (var "tp") $ Spine "iface" [var "imp"])
                    $ forall "cty" (forall "imp" (var "tp") $ forall "p" (Spine "iface" [var "imp"]) $ atom)
                    $ forall "exp" (forall "imp" (var "tp") $ forall "p" (Spine "iface" [var "imp"]) $ Spine "cty" [var "imp", var "p"])
                    $ open (var "closed") ("imp" ,var "tp") ("p",Spine "iface" [var "imp"]) atom (Spine "cty" [var "imp", var "p"])
                    )    
                    
         ]
         
test :: IO ()
test = case runError $ (\(a,_,_) -> a) <$> runRWST run (M.fromList consts) 0 of
  Left a -> putStrLn a
  Right sub -> putStrLn $ "success: "++show sub
  where run = do
          let constraint = (∃) "5" atom
                         $ (var "5") :=: (var "5" ~> atom)
                       :&: (var "5") :=: (atom ~> atom)
          runStateT (unify constraint) emptyContext


----------------------------
--- the public interface ---
----------------------------

startTypeCheck :: Constants -> String -> Type -> Choice ()    
startTypeCheck env str ty =  (\r -> (\(a,_,_) -> a) <$> runRWST r env 0) $ do 
  unless (getFamily ty == str) $ throwError $ "not the right family: "++show str++" = "++show ty
  constraint <- checkType ty atom
  substitution <- runStateT (unify constraint) emptyContext
  return ()
    
typeCheckPredicate :: Constants -> Predicate -> Choice Predicate
typeCheckPredicate env (Query nm ty) = appendErr ("in query : "++show ty) $ do
  startTypeCheck env "" ty
  return $ Query nm ty
typeCheckPredicate env pred@(Predicate pnm pty plst) = appendErr ("in\n"++show pred) $ do
  pty' <- appendErr ("in name: "++ pnm ++" : "++show pty) $
    startTypeCheck env "atom" pty
  plst' <- forM plst $ \(nm,ty) ->
    appendErr ("in case: " ++nm ++ " = "++show ty) $ (nm,) <$> startTypeCheck env pnm ty
  return $ Predicate pnm pty plst
  
typeCheckAll :: [Predicate] -> Choice [Predicate]
typeCheckAll preds = forM preds $ typeCheckPredicate assumptions
  where assumptions = M.fromList $ consts++
                      concatMap (\st -> case st of
                                    Query _ _ -> []
                                    _ -> (predName st, predType st):predConstructors st) preds
  
solver :: [(Name,Type)] -> Type -> Either String [(Name, Term)]
solver axioms tp = case runError $ runRWST (runStateT (search tp) emptyContext) (M.fromList axioms) 0 of
  Right (((s,tm),_),_,_) -> Right $ ("query", tm):(map (\a -> (a,var a)) $ S.toList $ freeVariables tp)
  Left s -> Left $ "reification not possible: "++s
