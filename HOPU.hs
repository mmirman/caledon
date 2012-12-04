{-# LANGUAGE 
 FlexibleContexts,  
 FlexibleInstances,
 ScopedTypeVariables,
 MultiParamTypeClasses, 
 UndecidableInstances,
 IncoherentInstances,
 TupleSections,
 DeriveFunctor
 #-}

module HOPU where

import Choice
import Data.Monoid
import Data.Maybe
import Data.Functor
import Control.Monad (void)
import Control.Applicative ((<|>), empty)
import Control.Monad.Error (ErrorT, throwError, runErrorT, lift, unless, when)
import Control.Monad.State (StateT, get, put, runStateT, modify)
import Control.Monad.State.Class
import Control.Monad.Writer (WriterT, runWriterT, listens)
import Control.Monad.Writer.Class
import Control.Monad.RWS (RWST, RWS, get, put, tell, runRWST, runRWS, ask)
import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.Trans.Class
import qualified Data.Map as M
import qualified Data.Set as S

data Variable = VarV Name 
              | ConsV Name 
              deriving (Ord, Eq, Show)

data Spine = Spine { binders :: [(Name,Tp)]
                   , head    :: Variable
                   , apps    :: [Spine] 
                   }
           deriving (Ord, Eq, Show)

infixr 5 :->:
data Tp = Atom Spine
        | Forall Name Tp Tp
        | Tp :->: Tp
        deriving (Eq, Ord)
                 
                 
rebuildSpine :: [(Name,Tp)] -> Spine -> [Spine] -> Spine
rebuildSpine binders = reb
  where reb (Spine [] c apps) apps' = Spine binders c (apps ++ apps')
        reb (Spine lst c apps) [] = Spine (binders++lst) c apps
        reb (Spine ((nm,_):l) c apps) (a:apps') = reb (substNm nm a $ Spine l c apps) apps'
  
substNm :: Name -> Spine -> Spine -> Spine
substNm nm s' = sub
  where sub s | any (==nm) $ binders s = s
        sub (Spine binders head apps) = let apps' = sub <$> apps in
          case head of 
            VarV nm' | nm == nm' -> rebuildSpine binders s' apps'
            _ -> Spine binders head apps'

type Substitution = M.Map Name Spine

class Subst a where
  subst :: Substitution -> a -> a
instance (Functor f , Subst a) => Subst (f a) where
  subst foo t = subst foo <$> t
instance Subst Spine where
  subst s (Spine ((a,t):l) head apps) = Spine ((a,subst s t):l) head' apps'
    where Spine l' head' apps' = subst (M.remove a s) $ Spine l head apps
  subst s (Spine [] head apps) = let apps' = subst s <$> apps  in
    case head of
      VarV nm | Just head' <- s ! nm -> rebuildSpine [] head' apps'
      _ -> Spine [] head apps'
      
instance Subst Tp where
  subst s t = case t of
    Atom t -> Atom $ subst s t
    Forall nm ty t -> Forall nm (subst s ty) $ subst (M.insert nm (Var nm) s) t
    ty1 :->: ty2 -> subst s ty1 :->: subst s ty2
instance Subst Judgement where 
  subst foo (c :|- s) = subst foo c :|- subst foo s


-----------------------------------------------------------------
----------------------- UNIFICATION -----------------------------
-----------------------------------------------------------------
class ConstraintGen m where
  putConstraints :: [Constraint Spine] -> m ()
instance Monad m => ConstraintGen (StateT St m) where
  putConstraints l = modify $ \s -> s { constraints = l++constraints s }  
instance MonadWriter [Constraint Spine] m => ConstraintGen m where  
  putConstraints = tell

data St = St { substitution :: Substitution
             , constraints :: [Constraint Spine]
             , variable :: Integer 
             } 

type Unify a = StateT St Choice a

class HasVar a where
  getV :: a -> Integer
  setV :: Integer -> a -> a
instance HasVar Integer where  
  getV = id
  setV a _ = a
instance HasVar St where  
  getV = variable  
  setV a st = st { variable = a}            
          
(+|->) :: Name -> Tm -> Unify ()
nm +|-> tm = modify $ \st -> st { substitution = M.insert nm tm $ subst (nm |-> tm) $ substitution st }

getNew :: (MonadState a m, HasVar a) => m Name
getNew = do 
  st <- get
  let n = 1 + getV st
  modify (setV n)
  return $! show n

nextConstraint :: ((Substitution, Constraint Tm) -> Unify ()) -> Unify ()
nextConstraint m = do
  st <- get
  case constraints st of
    [] -> return ()
    a:l -> do
      put $ st { constraints = l }
      m (substitution st,a)
      unify
      
unify :: Unify ()
unify = nextConstraint $ \(t, constraint@(a :=: b)) -> let
  badConstraint = throwError $ show constraint 
  in case (a :=: b) of
    _ :=: _ | a > b -> putConstraints [b :=: a]
    _ :=: _ -> badConstraint