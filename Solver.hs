{-# LANGUAGE 
 FlexibleContexts,  
 FlexibleInstances,
 TupleSections
 #-}
module Solver where

import AST
import Choice

import Control.Monad (void, unless)
import Control.Applicative ((<|>), empty)
import Control.Monad.Error.Class
import Control.Monad.State (StateT, runStateT)
import Control.Monad.Writer (WriterT, runWriterT)
import Control.Monad.Writer.Class
import Control.Monad.Trans.Class
import Data.Monoid
import Data.Functor
import Data.Traversable (forM)
import Data.Foldable as F (msum, foldr', foldl', foldl')
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

type VarGen = StateT Integer Choice

--------------------------------------------------------------------
----------------------- UNIFICATION --------------------------------
--------------------------------------------------------------------
type Unification = VarGen Substitution

getV = id
setV a _ = a
      
unifyAll _ _ [] = return mempty
unifyAll envE env (a:l) = do
  s <- appendErr ("UNIFYING CONSTRAINT: "++show a) $ unify envE env a
  (s ***) <$> unifyAll envE env (subst s l)

unify :: M.Map Name Tp -> M.Map Name Tp -> Constraint Tm -> Unification
unify envE env constraint@(a :=: b :@ from) = 
  let badConstraint :: VarGen a
      badConstraint = throwError $ show constraint
      unify'' c = unify envE env (c :@ from)
      unify' env c = unify envE env (c :@ from)
      doUntoBoth :: [Argument] -> [Argument] -> Unification
      doUntoBoth m n = F.foldl' act (return mempty) (zip (getTipe <$> m) (getTipe <$> n))
      act prev (mt,nt) = do
        sub <- prev 
        sub' <- unify' (subst sub env) $ subst sub $ toTm mt :=: toTm nt
        return $ sub *** sub'

      getTp :: Name -> Maybe Tp
      getTp nm = case env ! nm of
        Nothing -> envE ! nm
        Just t -> Just t
        
      getTmTp s = case getTipe s of
        Atom (Spine v []) | Just t <- getTp (getName v) -> return t
        Atom (Spine v []) -> Atom <$> var <$> getNew
        _ -> return $ atom
        
  in case a :=: b of
    _ :=: _ | a > b -> unify' env $ b :=: a
    
    AbsImp n ty t :=: _ -> do
      (v',s) <- solve $ (map (\(a,b)-> (Cons a,b)) $ M.toList envE)++(map (\(a,b)-> (Var a,b) )$ M.toList env) :|- ty
      unify' env $ subst (s *** n |-> v') t :=: subst s b
      
    Abs n ty t :=: Abs n' ty' t' -> do  
      s <- unify'' $ toTm ty :=: toTm ty'
      nm <- getNewWith $ "@abs=abs:"++n
      s' <- unify' (subst s $ M.insert nm ty env) $ subst (M.insert n (var nm) s) t :=: subst (M.insert n' (var nm) s) t'
      return $ s *** M.delete nm s'
    Abs n ty t :=: _ -> do  
      nm <- getNewWith $ "@abs=_:"++n
      s <- unify' (M.insert nm ty env) $ subst (n |-> var nm) t :=: rebuildSpine b [Norm $ Atom $ var nm]
      return $ M.delete nm s
    
    Spine (Var a) [] :=: Spine (Var a') [] | a == a' -> 
      return mempty
    Spine (Var a) [] :=: Spine (Var a') l | a == a' -> badConstraint
    Spine (Var a) [] :=: _ | not (M.member a env) && (not $ S.member a $ freeVariables b) -> 
      return $ a |-> b
    
    Spine (Var a) m :=: Spine (Var a') n | a == a' && M.member a env && length m == length n ->  -- the var has the same rule whether it is quantified or not.
      doUntoBoth m n
      
    Spine (Cons c) _ :=: Spine (Cons c') _ | c /= c' -> -- Const-Const /= 
      badConstraint
    Spine (Cons _) m :=: Spine (Cons _) n | length m == length n ->  -- Const-Const = 
      doUntoBoth m n
      
    Spine (Var x) n :=: Spine (Cons c) m | not $ M.member x env -> do -- Gvar-Const
      us <- forM n $ const $ getNewWith $ "@var=cons_L:"++x
      usty <- forM n getTmTp
      xs <- forM m $ const $ Var <$> (getNewWith $ "@var=cons_R:"++c)
      let l = Spine (Cons c) $ (\xi -> Norm $ Atom $ Spine xi $ Norm <$> Atom <$> var <$> us) <$> xs
          s = x |-> foldr' (\(v,ty) t -> Abs v ty t) l (zip us usty)
      s' <- unify' (subst s env) $ subst s (a :=: b)
      return $ (s *** s')
      
    Spine (Var a) n :=: Spine (Var a') m | a == a' && not (M.member a env) && length m == length n -> do
      h <- getNewWith $ "@var=var:"++a
      
      let act (xi, yi) next = do
            vi <- getNew

            sub' <- catchError (Just <$> unify'' (toTm xi :=: toTm yi)) $ \_ -> return Nothing

            (xs,zs,sub) <- next
            case sub' of
              Just sub' -> do 
                vit  <- getTmTp $ Norm xi
                return ((vi,vit):xs,vi:zs, sub' *** sub)              
              Nothing   -> do
                vit <- Atom <$> var <$> getNew
                return ((vi,vit):xs,zs  , sub)
                
      (xts,zs,sub) <- foldr' act (return (mempty, mempty, mempty)) (zip (getTipe <$> n) (getTipe <$> m))
      
      let xs = map fst xts
          base = Spine (Var h) (Norm <$> Atom <$> var <$> zs)
          f' = foldr' (\(v,xt) t -> Abs v xt t) base xts
      return (sub *** a |-> f')
      
    Spine (Var f) xs :=: Spine (Var g) ys | f /= g && xs == ys && not (M.member f env) && not (M.member g env) -> do
      return (g |-> var f)

    Spine (Var f) xs :=: Spine (Var g) ys | f /= g && not (M.member f env) && not (M.member g env) -> do -- Gvar-Gvar - diff
      h <- getNewWith $ "@var!=var:"++f++"&"++g
      let act xi next = do
            sub' <- flip catchError (const $ return Nothing) $ msum $ flip fmap ys $ \yi -> do
              sub <- unify'' (toTm xi :=: toTm yi)
              return $ Just (yi,sub)
            (zs,sub) <- next
            case sub' of
              Just (yi,sub') -> return ((xi,yi):zs, sub' *** sub)              
              Nothing  -> return (zs, sub)
      (zs,sub) <- foldr' act (return (mempty, mempty)) xs
      
      let toVar a@(Atom (Spine (Var x) [])) = do
            t <- getTmTp $ Norm a
            return (x, t)
          toVar _ = badConstraint
      
      xs' <- mapM toVar (getTipe <$> xs)
      ys' <- mapM toVar (getTipe <$> ys)
      
      let baseF = Spine (Var h) (fst <$> zs)
          f' = foldr' (\(v,vt) t -> Abs v vt t) baseF xs'
          
          baseG = Spine (Var h) (snd <$> zs)
          g' = foldr' (\(v,vt) t -> Abs v vt t) baseG ys'
      return (sub *** (f |-> f' *** g |-> g'))

    _ :=: _ -> badConstraint

genUnifyEngine env consts = do
  s <- unifyAll env mempty consts
  return $ finishSubst s
  
recSubst :: (Eq b, Subst b) => Substitution -> b -> b
recSubst s f = fst $ head $ dropWhile (not . uncurry (==)) $ iterate (\(_,b) -> (b,subst s b)) (f,subst s f)  

finishSubst s = recSubst s s

----------------------------------------------------------------------
----------------------- LOGIC ENGINE ---------------------------------
----------------------------------------------------------------------
type Reification = VarGen (Tm,Substitution)
type Deduction = VarGen Substitution

unifier :: [(Variable,Tp)] -> Tp -> Reification 
unifier cons t = do
  t' <- case t of
    Atom k -> return k
    _ -> empty
  let isAtom (Atom _) = True
      isAtom _ = False
  msum $ flip map (filter (isAtom . snd) cons) $ \(x,Atom con) -> do
    s <- genUnifyEngine (M.fromList $ (\(a,b) -> (getName a, b) ) <$> cons) [con :=: t' :@ show x]
    return $ (Spine x [],s) 

left :: Judgement -> Reification
left ([] :|- _) = empty
left ((x,f):context :|- r) = case f of
  Atom _ -> unifier [(x,f)] r
  ForallImp nm t1 t2 -> do
    nm' <- getNew
    y <- getNew
    (m,so) <- left $ (Var y,subst (nm |-> var nm') t2):context :|- r
    let n = case M.lookup nm' so of
          Nothing -> var nm'
          Just a -> a
        s = seq n $ M.delete nm' so
    s' <- natural (subst s $ (x,f):context) $ subst s (n,t1)
    return (subst s' $ subst (y |-> Spine x []) m, s *** s')
    
  Forall nm t1 t2 -> do
    nm' <- getNew
    y <- getNew
    (m,so) <- left $ (Var y,subst (nm |-> var nm') t2):context :|- r
    let n = case M.lookup nm' so of
          Nothing -> var nm'
          Just a -> a
        s = seq n $ M.delete nm' so
    s' <- natural (subst s $ (x,f):context) $ subst s (n,t1)
    return (subst s' $ subst (y |-> Spine x [Norm $ Atom n]) m, s *** s')

right :: Judgement -> Reification
right (context :|- r) = case r of
  Atom _ -> unifier context r
  ForallImp nm t1 t2 -> do
    nm' <- getNew
    (v,s) <- solve $ (Var nm', t1):context :|- subst (nm |-> cons nm') t2
    return $ (AbsImp nm' t1 v, s)
  Forall nm t1 t2 -> do
    nm' <- getNewWith $ "/f/" -- ++nm
    (v,s) <- solve $ (Var nm', t1):context :|- subst (nm |-> cons nm') t2
    return $ (Abs nm' t1 v, s)

solve :: Judgement -> Reification
solve judge@(context :|- r) = case r of
  Atom (Spine (Cons "atom") []) -> return (toTm atom, mempty) <|> soln
  _ -> soln
  where soln = right judge <|> (msum $ useSingle (\f ctx -> left $ f:ctx :|- r) context)
        useSingle f lst = sw id lst
          where sw _ [] = []
                sw placeOnEnd (a:lst) =  f a (placeOnEnd lst):sw (placeOnEnd . (a:)) lst

natural :: [(Variable, Tp)] -> (Tm,Tp) -> Deduction
natural cont (tm,ty) = do
  let env = M.fromList $ (\(a,b) -> (getName a, b)) <$> cont
  (_, constraints) <- runWriterT $ checkTipe env tm ty
  genUnifyEngine env constraints
  

solver :: [(Variable,Tp)] -> Tp -> Either String [(Name, Tm)]
solver axioms t = case runError $ runStateT (solve $ axioms :|- t) 0 of
  Right ((tm,s),_) -> Right $ ("query", tm):(recSubst s $ map (\a -> (a,var a)) $ S.toList $ freeVariables t)
  Left s -> Left $ "reification not possible: "++s
  
-----------------------------------------------------------------
----------------------- Type Checker ----------------------------    
-----------------------------------------------------------------
type Environment = M.Map Name Tp
type NatDeduct = WriterT [Constraint Tm] VarGen

class CheckType t where
  checkTipe :: Environment -> t -> Tp -> NatDeduct Tp
  
instance CheckType Variable where
  checkTipe env v t = case v of
    Cons nm -> case env ! nm of
      Nothing -> error $ nm++" was not found in the environment in "++show v++" : "++show t
      Just t' -> do
        tell [toTm t' :=: toTm t :@ show v]
        return t'
    Var nm -> case env ! nm of
      Nothing -> throwError $ nm++" was not found in the environment in "++show v++" : "++show t
      
      Just t' -> do
        tell [toTm t' :=: toTm t :@ show v]
        return t'
      
instance CheckType Tm where
  checkTipe env oldBody t = case oldBody of
    Spine a l -> do
      tv1  <- getNewWith $ ':':show a
      tv2l <- forM l $ \b -> do
        bty <- getNewWith $ "@bty"
        t'  <- checkTipe env (getTipe b) $ Atom $ var bty
        return $ b { getTipe = t'} 
      
      tv1' <- checkTipe env a $ Atom $ var $ tv1
    
      tell [ rebuildSpine (toTm tv1') tv2l :=: toTm t :@ show oldBody]
      return t
    AbsImp nm nmTy body -> do  
      checkTipe env nmTy atom
      v1  <- getNewWith $ ":<"++nm
      v2  <- getNewWith $ ":>"++nm
      tell [ toTm (ForallImp v1 nmTy $ Atom $ var v2) :=: toTm t :@ show oldBody]
      ForallImp v1 nmTy <$> intermediateUnify env oldBody (nm,nmTy) (body, Atom $ var v2)
      
    Abs nm nmTy body -> do
      checkTipe env nmTy atom
      v1  <- getNewWith $ ":<"++nm
      v2  <- getNewWith $ ":>"++nm
      tell [ toTm (Forall v1 nmTy $ Atom $ var v2) :=: toTm t :@ show oldBody]
      Forall v1 nmTy <$> intermediateUnify env oldBody (nm,nmTy) (body, Atom $ var v2)

intermediateUnify env oldBody (nm, nmTy) (body, bodyTipe) = do
  nm' <- getNewWith $ '*':nm
  (t',constraints) <- listen $ checkTipe (M.insert nm' nmTy env) (subst (nm |-> cons nm') body) bodyTipe
  s <- lift $ genUnifyEngine env constraints
  let sub = flip M.mapMaybe (M.delete nm' s) $ \t -> case S.member nm' $ allConstants t  of
        True -> Nothing
        False -> Just t
      fv = freeVariables oldBody
      sub' = flip M.mapMaybeWithKey sub $ \k t -> case S.member k fv of
        True -> Just t
        False -> Nothing
            
  tell $ map (\(s',t) -> var s' :=: t :@ show oldBody) $ M.toList sub'   
  return t'
  
instance CheckType Tp where
  checkTipe env oldBody atomty = checkTipe env (toTm oldBody) atomty

getCons tm = case tm of
  Spine (Cons t) _ -> return t
  Abs _ _ t -> getCons t
  _ -> throwError $ "can't place a non constructor term here: "++ show tm

getPred tp = case tp of
  Atom t -> getCons t
  Forall _ _ t -> getPred t
  ForallImp _ _ t -> getPred t

getNewWith t = (++t) <$> getNew

-- need to do a topological sort of types and predicates.
-- such that types get minimal correct bindings
checkType :: Environment -> Name -> Tp -> Choice Tp
checkType env base ty = fmap fst $ flip runStateT 0 $ appendErr ("FOR: "++show ty) $ do
  con <- getPred ty
  unless (null base || con == base) 
    $ throwError $ "non local name \""++con++"\" expecting "++base

  let fv = freeVariables ty  
      
  fvTy <- M.fromList <$> mapM (\i -> (i,) <$> Atom <$> var <$> getNew) (S.toList fv)
  let envWF = mappend env fvTy 
      
  (_,constraints) <- runWriterT $ checkTipe envWF ty atom
  
  s <- genUnifyEngine envWF constraints

  let envWFL = (\(a,l) -> (Cons a, l)) <$> M.toList env
      act :: (Name, Tp) -> VarGen Substitution -> VarGen Substitution
      act (nm,tyVar) sub = trace ("WHICH WAS: "++nm++" : "++show tyVar) $ do
        s <- sub
        let tyVar' = toTp $ subst s tyVar
        (imp,s') <- trace ("WHILE RESOLVING: "++show tyVar'++"\nWITH SUBST: "++show (M.toList s) ++ "\nWITH ENV:"++show envWFL) $ solve $ envWFL :|- tyVar'
        trace ("WHICH BECAME: "++show imp) $ return (s *** s' *** nm |-> imp)
      fvTyL = M.toList fvTy
  s' <- foldr' act (return s) fvTyL

  -- I'm not sure this makes sense at all.
  -- in the mean time, assume there is only one use of each unbound variable
  
  return $ subst s' ty

typeCheckPredicate :: Environment -> Predicate -> Choice Predicate
typeCheckPredicate env (Query nm ty) = appendErr ("in query : "++show ty) $ do
  void $ checkType env "" ty
  return $ Query nm ty
typeCheckPredicate env pred@(Predicate pnm pty plst) = appendErr ("in\n"++show pred) $ do
  pty' <- appendErr ("in name: "++ pnm ++" : "++show pty) $
    checkType env "atom" pty
  plst' <- forM plst $ \(nm,ty) -> 
    appendErr ("in case: " ++nm ++ " = "++show ty) $ (nm,) <$> checkType env pnm ty
  return $ Predicate pnm pty' plst'

typeCheckAll :: [Predicate] -> Choice [Predicate]
typeCheckAll preds = forM preds $ typeCheckPredicate assumptions
  where assumptions = M.fromList $ 
                      ("atom", atom): -- atom : atom is a given.
                      ("forall", (atom ~~> atom) ~~> atom): -- atom : atom is a given.                      
                      ("?forall", (atom ==> atom) ~~> atom): -- atom : atom is a given.
                      concatMap (\st -> case st of
                                    Query _ _ -> []
                                    _ -> (predName st, predType st):predConstructors st) preds
