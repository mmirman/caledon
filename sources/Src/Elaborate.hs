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
import Control.Monad.RWS.Lazy (RWS, ask, local, censor, runRWS, censor, tell, get, put, listen, lift)
import Control.Monad.State.Class (MonadState(), get, modify)
import Control.Spoon
import Data.Monoid

type TypeChecker = RWS Ctxt Form Int

typeConstraints cons tm ty = evalGen (do new <- Pat <$> getNewExists "@head" ty
                                         genConstraintN tm new ty
                                         return new
                                     ) cons

evalGen m cons = do
  s <- get 
  let ~(a,s',f) = runRWS m (emptyCon cons) s
  put s'
  return (a,f)

getNewExists :: String -> Type -> TypeChecker P
getNewExists s ty = do
  nm <- getNewWith s
  depth <- height <$> ask 
  return $ Var $ Exi depth nm ty

bindForall :: Type -> TypeChecker a -> TypeChecker a  
bindForall ty = censor (bind ty) . local (\a -> putTy a ty)

(.=.) a b  = tell $ a :=: b
(.<.) a b  = tell $ a :<: b
(.<=.) a b = tell $ a :<=: b
(.@.) a b  = tell $ a :@: b

getNewTyVar :: String -> TypeChecker P
getNewTyVar t = do
  v <- getNewWith "@tmake"
  getNewExists t (tipemake v)

genConstraintN :: N -> N -> Type -> TypeChecker ()
genConstraintN n n' ty = case n of
  Abs tyAorg sp -> do
    tyA <- getNewTyVar "@tyA"
    genConstraintTy tyAorg tyA

    case viewForallP ty of
      Just ~(tyA',tyF') -> do
        Pat tyA .=. Pat tyA'
        bindForall tyA $ 
          genConstraintN sp (appN' (liftV 1 n') $ var 0) tyF'
      _ -> do
        v1 <- getNewWith "@tmake1"
        e <- getNewExists "@e" (forall (liftV 1 tyA) $ tipemake v1)
        let body = e :+: var 0
        Pat (forall tyA body) .<=. Pat ty
        bindForall tyA $ 
          genConstraintN sp (appN' (liftV 1 n') $ var 0) body
      
  Pat p -> do
    ty' <- case n' of
      Pat p' -> genConstraintP p p'
      _ -> do
        p' <- getNewExists "@spB" ty
        Pat p' .=. n'
        genConstraintP p p'
    Pat ty' .<=. Pat ty

genConstraintTy :: Type -> Type -> TypeChecker ()
genConstraintTy p r = do
  ~b <- genConstraintP p r
  v1 <- getNewWith "@tmake0"
  Pat b .=. Pat (tipemake v1)
  
genConstraintP :: P -> P -> TypeChecker Type
genConstraintP p p' = case p of 

  (viewForallP -> Just ~(tyAorg,tyF)) -> do

    tyA <- getNewTyVar "@tyA"
    tyret <- tipemake <$> getNewWith "@ret"
    tyAty <- genConstraintP tyAorg tyA
    Pat tyAty .<=. Pat tyret
    
    tyFf' <- (getNewExists "@fbody" . forall tyA . tipemake) =<< getNewWith "@tmakeF"
    bindForall tyA $ do
      tyFty <- genConstraintP tyF (liftV 1 tyFf' :+: var 0)
      Pat tyFty .<=. Pat (liftV 1 tyret)
      
    Pat (forall tyA $ liftV 1 tyFf' :+: var 0) .=. Pat p'
    
    return tyret
  (tipeView -> Init v1) -> do
    v2 <- getNewWith "@tmakeA"
    Pat (tipemake v1) .<. Pat (tipemake v2)
    Pat (tipemake v1) .=. Pat p'
    return $ tipemake v2

  (tipeView -> Uninit) -> do
    v1 <- getNewWith "@tmakeB"
    v2 <- getNewWith "@tmakeC"
    Pat (tipemake v1) .<. Pat (tipemake v2)
    Pat (tipemake v1) .=. Pat p'
    return $ tipemake v2

  forg :+: vorg -> do
    tyArg <- getNewTyVar "@ftyArg"
    tyVal <- getNewWith "@ftyValmake"
    tyBody <- getNewExists "@ftyBody" (tyArg ~> tipemake tyVal)
    
    let tyF' = tyArg ~> (liftV 1 tyBody :+: var 0)
    f   <- getNewExists "@fex" tyF'
    
    tyF <- genConstraintP forg f
    Pat tyF .<=. Pat tyF'
    
    v <- Pat <$> getNewExists "@tyV" tyArg
        
    genConstraintN vorg v tyArg
    Pat (f :+: v) .=. Pat p'
    return $ tyBody :+: v
    
  Var (Con "#hole#") -> do
    ty <- getType p'
    Pat p' .@. ty
    return ty

  Var a -> do
    ctxt <- ask
    getVal ctxt a .=. Pat p'
    return $ getTy ctxt a 


getType (Var v) = do
  ctxt <- ask
  return $ getTy ctxt v
getType (a :+: v) = do
  x <- getType a
  case viewForallP x of
    Nothing -> do
      l <- getNewWith   "@tmakeF"
      l' <- getNewWith   "@tmakeF"
      ty <- getNewExists "@xty" $ tipemake l
      tyBody <- getNewExists "@ftyBody" (ty ~> tipemake l')
      Pat x .=. Pat (forall ty (tyBody :+: var 0))
      return (tyBody :+: v)
    Just ~(ty,t') -> do
      return $ fromType $ appN' (Abs ty $ Pat t') v

    