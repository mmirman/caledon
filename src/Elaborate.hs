{-# LANGUAGE  
 ViewPatterns
 #-}
module Src.Elaborate (typeConstraints) where

import Src.Variables
import Src.AST 
import Src.Context
import Src.FormulaSequence
import Src.Substitution
import Data.Functor
import Control.Monad.RWS.Lazy (RWS, ask, local, censor, runRWS, censor, tell)
import Control.Monad.State.Class (MonadState(), get, modify)

type TypeChecker = RWS Ctxt Form Integer

typeConstraints cons tm ty = evalGen (genConstraintN tm ty) cons 

evalGen :: (Functor m, MonadState c m, ValueTracker c) 
           => TypeChecker a -> Constants -> m (a,Form)
evalGen m cons = do
  i <- takeValue <$> get 
  let ~(a,s,f) = runRWS m (emptyCon cons) i
  modify $ putValue s
  return (a,f)

getNewExists s ty = do
  nm <- getNewWith s
  depth <- height <$> ask 
  return $ Var $ Exi depth nm ty

bindForall :: Type -> TypeChecker a -> TypeChecker a
bindForall ty = censor (Bind ty) . local (\a -> putTy a ty)

(.=.) a b = tell $ a :=: b
(.<.) a b = tell $ a :<: b
(.<=.) a b = tell $ a :<=: b
(.@.) a b = tell $ a :@: b

genConstraintN :: N -> Type -> TypeChecker Term
genConstraintN n ty = case n of
  Abs tyA sp -> case viewForallP ty of
    Just ~(tyA',tyF') -> do
      tyA <- genConstraintTy tyA
      Pat tyA .=. Pat tyA'
      bindForall tyA $ do
        Abs tyA <$> genConstraintN sp tyF'
    _ -> do
      tyA <- genConstraintTy tyA
      e <- getNewExists "@e" (forall tyA tipe)
      
      let body = e :+: var 0
      Pat (forall tyA body) .<=. Pat ty
      Abs tyA <$> bindForall tyA (genConstraintN sp body)
  Pat p -> do
    ~(p,ty') <- genConstraintP p
    Pat ty' .<=. Pat ty
    return $ p

genConstraintTy :: Type -> TypeChecker Type
genConstraintTy p = do
  ~(a , b) <- genConstraintP p
  Pat b .=. Pat tipe
  return $ fromType a
  
genConstraintP :: P -> TypeChecker (Term, Type)
genConstraintP p = case p of 
  (viewForallP -> Just ~(tyA,tyF)) -> do
    ~(tyA, tyAty) <- genConstraintP tyA
    
    let tyA' = fromType tyA
    tyret <- tipemake <$> getNewWith "@maketipe"
    Pat tyAty .<=. Pat tyret
    
    ~(tyF, tyFty) <- bindForall tyA' $ genConstraintP tyF
    Pat tyFty .<=. Pat tyret
    
    return (Pat $ forall tyA' (fromType tyF), tyret)
  (tipeView -> Init v1) -> do
    v2 <- getNewWith "@tmake"
    Pat (tipemake v1) .<. Pat (tipemake v2)
    return (Pat $ tipemake v1, tipemake v2)
  (tipeView -> Uninit) -> do
    v1 <- getNewWith "@tmake"
    v2 <- getNewWith "@tmake"
    Pat (tipemake v1) .<. Pat (tipemake v2)
    return (Pat $ tipemake v1 , tipemake v2)
  f :+: v -> do
    ~(f,tyF) <- genConstraintP f 
    case viewForallP tyF of
      Just ~(tyV,tyR) -> do
        v <- genConstraintN v tyV
        ctxt <- ask
        let tyR' = appN ctxt (Abs tyV $ Pat tyR) v
        return (appN ctxt f v, fromType tyR')
      Nothing -> do
        x <- getNewExists "@xin" tipe
        let tybodyty = forall x tipe
        tybody <- getNewExists "@tybody" tybodyty
        Pat tyF .<=. Pat (forall x $ tybody :+: var 0)
        v <- genConstraintN v x
        ctxt <- ask
        return (appN ctxt f v, tybody :+: v)
  Var a -> do
    ctxt <- ask
    return (getVal ctxt a, getTy ctxt a)
    
    -- I just need to share the graph!!!!
    -- Then I only have to generate variable names once!
    -- unfortunately, this means that the graph might become GIANT!
    -- which is bad.
    -- Fortunately, it might be the case that the graph is either
    -- always highly disconnected or highly connected.