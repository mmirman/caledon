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
import Control.Monad.RWS.Lazy (RWS, ask, local, censor, runRWS, censor, tell, get, put, listen)
import Control.Monad.State.Class (MonadState(), get, modify)
import Control.Spoon
import Data.Monoid
type TypeChecker = RWS Ctxt Form Int

typeConstraints cons tm ty = evalGen (genConstraintN tm ty) cons 

evalGen m cons = do
  s <- get 
  let ~(a,s',f) = runRWS m (emptyCon cons) s
  put s'
  return (a,f)

getNewExists s ty = do
  nm <- getNewWith s
  depth <- height <$> ask 
  return $ Var $ Exi depth nm ty

  
bindForall ty m = censor (bind ty) $ local (\a -> putTy a ty) m


(.=.) a b  = tell $ a :=: b
(.<.) a b  = tell $ a :<: b
(.<=.) a b = tell $ a :<=: b
(.@.) a b  = tell $ a :@: b

genConstraintN :: N -> Type -> TypeChecker Term
genConstraintN n ty = case n of
  Abs tyA sp -> do
    tyA <- genConstraintTy tyA
    Abs tyA <$> case viewForallP ty of
      Just ~(tyA',tyF') -> do
        Pat tyA .=. Pat tyA'
        bindForall tyA $ genConstraintN sp tyF'
      _ -> do
        v1 <- getNewWith "@tmake1"
        e <- getNewExists "@e" (forall (liftV 1 tyA) $ tipemake v1)
        let body = e :+: var 0
        Pat (forall tyA body) .<=. Pat ty
        bindForall tyA $ genConstraintN sp body
        
  Pat p -> do
    ~(p,ty') <- genConstraintP p
    Pat ty' .<=. Pat ty
    return p

genConstraintTy :: Type -> TypeChecker Type
genConstraintTy p = do
  ~(a , b) <- genConstraintP p
  v1 <- getNewWith "@tmake0"
  
  Pat b .=. Pat (tipemake v1)
  return $ fromType a
  
genConstraintP :: P -> TypeChecker (Term, Type)
genConstraintP p = case p of 
  (viewForallP -> Just ~(tyA,tyF)) -> do
    
    ~(tyA, tyAty) <- genConstraintP tyA
    
    let tyA' = fromType tyA
    tyret <- tipemake <$> getNewWith "@maketipe"
    Pat tyAty .<=. Pat tyret
    
    tyF <- bindForall tyA' $ do
      ~(tyF, tyFty) <- genConstraintP tyF
      Pat tyFty .<=. Pat tyret    
      return tyF
    
    return (Pat $ forall tyA' (fromType tyF), tyret)
  (tipeView -> Init v1) -> do
    v2 <- getNewWith "@tmakeA"
    Pat (tipemake v1) .<. Pat (tipemake v2)
    return (Pat $ tipemake v1, tipemake v2)
  (tipeView -> Uninit) -> do
    v1 <- getNewWith "@tmakeB"
    v2 <- getNewWith "@tmakeC"
    Pat (tipemake v1) .<. Pat (tipemake v2)
    return (Pat $ tipemake v1 , tipemake v2)
  f :+: v -> do
    ~(f,tyF) <- genConstraintP f 
    case viewForallP tyF of
      Just ~(tyV,tyR) -> do
        v <- genConstraintN v tyV
        let tyR' = appN' (Abs tyV $ Pat tyR) v
        ctxt <- ask
        return (appN ctxt f v, fromType tyR')
      Nothing -> do
        v1 <- getNewWith "@tmakeD"
        v2 <- getNewWith "@tmakeE"
        
        x <- getNewExists "@xin" (tipemake v1)
        v <- genConstraintN v x
        let tybodyty = forall x (tipemake v2)
        tybody <- getNewExists "@tybody" tybodyty
        Pat tyF .<=. Pat (forall x $ tybody :+: var 0)
        ctxt <- ask
        return (appN ctxt f v,  tybody :+: v)
  Var (Con "#hole#") -> do
    v <- getNewWith   "@tmakeF"
    ty <- getNewExists "@xty" $ tipemake v
    e  <- getNewExists "@xin" ty
    return (Pat e, ty)
  Var a -> do
    ctxt <- ask
    -- what the ever loving FUCK???
    return (getVal ctxt a, liftV 1 $ getTy ctxt a) 
      
    
    -- I just need to share the graph!!!!
    -- Then I only have to generate variable names once!
    -- unfortunately, this means that the graph might become GIANT!
    -- which is bad.
    -- Fortunately, it might be the case that the graph is either
    -- always highly disconnected or highly connected.




{-
∀: type ( #%#25@tmakeB )  . 
47@tybody<2> ( 0 ( λ:1 . (λ:2 . (0)) )  )  ≤ type ( #%#31@maketipe )

∀: [ [ 0 ]  [ 1 ]  2 ]  1 
. type ( #%#9@tmakeB )  ≤ [ 34@xin<2> ]  35@tybody<2> ( 0 )
∧ type ( #%#25@tmakeB )  ≤ 34@xin<2> 

∧ 35@tybody<2> ( 1 )  ≤ [ 38@xin<2> ]  39@tybody<2> ( 0 )  
∧ type ( #%#6@tmakeB )  ≤ 38@xin<2>

∧  39@tybody<2> ( type ( #%#3@tmakeB )  )  ≤ [ 42@xin<2> ]  43@tybody<2> ( 0 )
∧ [ [ 0 ]  [ 1 ]  2 ]  1 ≤ 42@xin<2>

∧ 43@tybody<2> ( 0 )  ≤ [ 46@xin<2> ]  47@tybody<2> ( 0 )
∧ 1 ≐ 0  
∧ 0 ≤ 46@xin<2>
∧ ∀: 1 . (  ( 2 ≐ 1 ) ∧ (  ∀: 2 . 2 ≤ 2 ) )
-}