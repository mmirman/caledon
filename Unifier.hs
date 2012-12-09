{-# LANGUAGE 
 FlexibleContexts,  
 FlexibleInstances,
 TupleSections
 #-}
module Unifier where

import AST
import Choice
import Control.Monad (void)
import Control.Applicative ((<|>), empty)
import Control.Monad.Error (throwError, catchError)
import Control.Monad.State (StateT, get, put, runStateT, modify)
import Control.Monad.State.Class
import Control.Monad.Trans.Class
import Data.Monoid
import Data.Functor
import Data.Traversable (forM)
import Data.Foldable as F (msum, forM_, fold, Foldable, foldl', foldr')
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace
--------------------------------------------------------------------
----------------------- UNIFICATION --------------------------------
--------------------------------------------------------------------
type VarGen = StateT Integer Choice


class HasVar a where
  getV :: a -> Integer
  setV :: Integer -> a -> a
instance HasVar Integer where  
  getV = id
  setV a _ = a
      
unifyAll env [] = return mempty
unifyAll env (a:l) = do
  s <- appendErr ("IN: "++show a) $ unify env a
  s' <- unifyAll env (subst s l)
  return $ s *** s'

unify :: M.Map Name Tp -> Constraint Tm -> VarGen Substitution
unify env constraint@(a :=: b) = 
  let badConstraint = throwError $ show constraint ++" \nWITH: "++show (M.toList env)
      unify' = unify env
      doUntoBoth m n = F.foldl' act (return mempty) (zip m n)
      act prev (mt,nt) = do
        sub <- prev 
        sub' <- unify (subst sub env) $ subst sub (tpToTm mt :=: tpToTm nt)
        return $ sub *** sub'

  in case a :=: b of
    _ :=: _ | a > b -> unify env $ b :=: a
    AbsImp n ty t :=: AbsImp n' ty' t' -> do
      s <- unify' $ tpToTm ty :=: tpToTm ty'
      nm <- getNew
      s' <- unify (subst s $ M.insert nm ty env) $ subst (M.insert n (var nm) s) t :=: subst (M.insert n' (var nm) s) t'
      return $ s *** M.delete nm s'
    Abs n ty t :=: Abs n' ty' t' -> do  
      s <- unify' $ tpToTm ty :=: tpToTm ty'
      nm <- getNew
      s' <- unify (subst s $ M.insert nm ty env) $ subst (M.insert n (var nm) s) t :=: subst (M.insert n' (var nm) s) t'
      return $ s *** M.delete nm s'
    Abs n ty t :=: _ -> do  
      nm <- getNew
      s <- unify (M.insert nm ty env) $ subst (n |-> var nm) t :=: rebuildSpine b [Atom $ var nm]
      return $ M.delete nm s
    
    Spine (Var a) [] :=: Spine (Var a') [] | a == a' -> 
      return mempty
    Spine (Var a) [] :=: _ | not (M.member a env) && (not $ S.member a $ freeVariables b) -> 
      return $ a |-> b
    Spine (Var a) m :=: Spine (Var a') n | a == a' && M.member a env && length m == length n ->  -- the var has the same rule whether it is quantified or not.
      doUntoBoth m n
      
    Spine (Cons c) _ :=: Spine (Cons c') _ | c /= c' -> 
      badConstraint
    Spine (Cons c) m :=: Spine (Cons c') n | length m == length n -> 
      doUntoBoth m n
      
    Spine (Var x) n :=: Spine (Cons c) m | not $ M.member x env -> do -- Gvar-Const
      us <- forM n $ const $ getNew
      usty <- forM n $ const $ Atom <$> var <$> getNew
      xs <- forM m $ const $ Var <$> getNew
      let l = Spine (Cons c) $ (\xi -> Atom $ Spine xi $ Atom <$> var <$> us) <$> xs
          s = x |-> foldr' (\(v,ty) t -> Abs v ty t) l (zip us usty)
      s' <- unify (subst s env) $ subst s (a :=: b)
      return $ (s *** s')
      
    Spine (Var a) n :=: Spine (Var a') m | a == a' && length m == length n -> do -- Gvar-Gvar - same
      h <- getNew
      let act (xi, yi) next = do
            vi <- getNew
            sub' <- catchError (Just <$> unify' (tpToTm xi :=: tpToTm yi)) $ \_ -> return Nothing
            (xs,zs,sub) <- next
            case sub' of
              Just sub' -> return (vi:xs,vi:zs, sub' *** sub)              
              Nothing   -> return (vi:xs,zs, sub)
                
      (xs,zs,sub) <- foldr' act (return (mempty, mempty, mempty)) (zip n m)
      
      let base = Spine (Var h) (Atom <$> var <$> zs)
          f' = foldr' (\v t -> Abs v undefined t) base xs
      return (sub *** a |-> f')
      
    Spine (Var f) xs :=: Spine (Var g) ys | f /= g -> do -- Gvar-Gvar - diff
      h <- getNew
      let act xi next = do
            sub' <- flip catchError (const $ return Nothing) $ msum $ flip fmap ys $ \yi -> do
              sub <- unify' (tpToTm xi :=: tpToTm yi)
              return $ Just (yi,sub)
            (zs,sub) <- next
            case sub' of
              Just (yi,sub') -> return ((xi,yi):zs, sub' *** sub)              
              Nothing  -> return (zs, sub)
      (zs,sub) <- foldr' act (return (mempty, mempty)) xs
      
      let toVar (Atom (Spine (Var x) [])) = do
            t <- getNew
            return (x, Atom $ var t)
          toVar _ = badConstraint
      
      xs' <- mapM toVar xs
      ys' <- mapM toVar ys
      
      let baseF = Spine (Var h) (fst <$> zs)
          f' = foldr' (\(v,vt) t -> Abs v vt t) baseF xs'
          
          baseG = Spine (Var h) (snd <$> zs)
          g' = foldr' (\(v,vt) t -> Abs v vt t) baseG ys'
      return (sub *** (f |-> f' *** g |-> g'))
{-    Spine (Var a) n :=: Spine (Var a') m | a /= a' -> do -- Gvar-Gvar - diff
      h <- getNew
      let act (xi, yi) next = do
            vi <- getNew
            sub' <- catchError (Just <$> unify' (tpToTm xi :=: tpToTm yi)) $ \_ -> return Nothing
            (xs,zs,sub) <- next
            case sub' of
              Just sub' -> return (vi:xs,vi:zs, sub' *** sub)              
              Nothing   -> return (vi:xs,zs, sub)
                
      (xs,zs,sub) <- foldr' act (return (mempty, mempty, mempty)) (zip n m)
      
      let base = Spine (Var h) (Atom <$> var <$> zs)
          f' = foldr' (\v t -> Abs v undefined t) base xs
      return (sub *** a |-> f')
-}
      -- I need to keep track of levels in the environment! 
      
    _ :=: _ -> badConstraint

genUnifyEngine consts = do
  s <- unifyAll mempty consts
  return $ finishSubst s
  
recSubst :: (Eq b, Subst b) => Substitution -> b -> b
recSubst s f = fst $ head $ dropWhile (not . uncurry (==)) $ iterate (\(_,b) -> (b,subst s b)) (f,subst s f)  

finishSubst s = recSubst s s

finishSubstWith w s = case M.lookup w s of
  Just (Spine (Var v) []) -> finishSubst $ M.insert v (var w) (M.delete w s)
  _ -> s


