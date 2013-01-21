{-# LANGUAGE
 DeriveFunctor,
 FlexibleInstances,
 PatternGuards
 #-}

module AST where

import qualified Data.Foldable as F
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Functor
import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.Set as S
import Control.Monad.RWS (RWST, runRWST, ask, withRWST)
import Control.Monad.Trans (lift)
import Choice

-----------------------------
---  abstract syntax tree ---
-----------------------------

type Name = String

infixr 0 ~>
(~>) = forall ""

data Spine = Spine Name [Type]
           | Abs Name Type Spine 
           deriving (Eq)

type Type = Spine
type Term = Spine

data Predicate = Predicate { predName :: Name, predType :: Type, predConstructors :: [(Name,Type)] }
               | Query { predName :: Name, predType ::  Type }
               deriving (Eq)


getNewWith s = (++s) <$> getNew

showWithParens t = if (case t of
                          Abs{} -> True
                          Spine _ lst -> not $ null lst
                      ) then "("++show t++")" else show t 

instance Show Spine where
  show (Spine "forall" [_,Abs nm t t']) | not (S.member nm (freeVariables t')) = showWithParens t++ " → " ++ show t'
  show (Spine "forall" [_,Abs nm ty t]) = "∀ "++nm++" : "++showWithParens ty++" . "++show t  
  show (Spine "exists" [_,Abs nm ty t]) = "∃ "++nm++" : "++showWithParens ty++" . "++show t  
  show (Spine h t) = h++concatMap (\s -> " "++showWithParens s) t
  show (Abs nm ty t) = "λ "++nm++" : "++showWithParens ty++" . "++show t

instance Show Predicate where
  show (Predicate nm ty []) = "defn " ++ nm ++ " : " ++ show ty ++ ";"
  show (Predicate nm ty (a:cons)) =
    "defn " ++ nm ++ " : " ++ show ty ++ "\n" ++ "  as " ++ showSingle a ++ concatMap (\x-> "\n   | " ++ showSingle x) cons ++ ";"
      where showSingle (nm,ty) = nm ++ " = " ++ show ty
  show (Query nm ty) = "query " ++ nm ++ " = " ++ show ty
                                               
var nm = Spine nm []
atom = var "atom"
forall x tyA v = Spine ("forall") [tyA, Abs x tyA v]
exists x tyA v = Spine ("exists") [tyA, Abs x tyA v]


---------------------
---  substitution ---
---------------------

type Substitution = M.Map Name Spine

infixr 1 |->
infixr 0 ***
m1 *** m2 = M.union m2 $ subst m2 <$> m1
(|->) = M.singleton
(!) = flip M.lookup

rebuildSpine :: Spine -> [Spine] -> Spine
rebuildSpine s [] = s
--rebuildSpine (Spine "forall" [a]) apps' = rebuildSpine a apps'
rebuildSpine (Spine c apps) apps' = Spine c (apps ++ apps')
rebuildSpine (Abs nm _ rst) (a:apps') = rebuildSpine (subst (nm |-> a) $ rst) apps'

newName nm s = (nm',s')
  where s' = if nm == nm' then s else M.insert nm (var nm') s 
        nm' = fromJust $ find free $ nm:map (\s -> show s ++ "/") [0..]
        fv = mappend (M.keysSet s) (freeVariables s)
        free k = not $ S.member k fv

class Subst a where
  subst :: Substitution -> a -> a
instance Subst a => Subst [a] where
  subst foo t = subst foo <$> t
instance (Subst a, Subst b) => Subst (a,b) where
  subst foo (a,b) = (subst foo a , subst foo b)
instance Subst Spine where
  subst s (Abs nm tp rst) = Abs nm' (subst s tp) $ subst s' rst
    where (nm',s') = newName nm s
  subst s (Spine nm apps) = let apps' = subst s <$> apps  in
    case s ! nm of
      Just nm -> rebuildSpine nm apps'
      _ -> Spine nm apps'

class FV a where         
  freeVariables :: a -> S.Set Name
instance (FV a, F.Foldable f) => FV (f a) where
  freeVariables m = F.foldMap freeVariables m
instance FV Spine where
  freeVariables t = case t of
    Abs nm t p -> (S.delete nm $ freeVariables p) `mappend` freeVariables t
    Spine head others -> mappend (S.singleton head) $ mconcat $ freeVariables <$> others

-------------------------
---  traversal monads ---
-------------------------
type Constants = Map Name Type

type Env = RWST Constants () Integer Choice

lookupConstant x = (M.lookup x) <$> lift ask 

addToEnv x ty = withRWST $ \r s -> (M.insert x ty r, s) 

-------------------------
---  Constraint types ---
-------------------------

data Quant = Forall | Exists deriving (Eq) 

instance Show Quant where
  show Forall = "∀"
  show Exists = "∃"

-- as ineficient as it is, I'll make this the constraint representation.
infixr 2 :=:  
infixr 1 :&:

data Constraint = Top
                | Spine :=: Spine
                | Constraint :&: Constraint
                | Bind Quant Name Type Constraint
                deriving (Eq)
                         
instance Show Constraint where
  show (a :=: b) = show a ++" ≐ "++show b
  show (a :&: b) = show a ++" ∧ "++show b
  show Top = " ⊤ "
  show (Bind q n ty c) = show q++" "++ n++" : "++show ty++" . "++showWithParens c
    where showWithParens Bind{} = show c
          showWithParens _ = "( "++show c++" )"

instance Subst Constraint where
  subst s (s1 :=: s2) = subst s s1 :=: subst s s2
  subst s (c1 :&: c2) = subst s c1 :&: subst s c2
  subst s (Bind q nm t c) = Bind q nm' (subst s t) $ subst s' c
    where (nm',s') = newName nm s
          

(∃) = Bind Exists
(∀) = Bind Forall


class RegenAbsVars a where
  regenAbsVars :: a -> Env a
instance RegenAbsVars Constraint where  
  regenAbsVars cons = case cons of
    Bind q nm ty cons -> do
      ty' <- regenAbsVars ty
      Bind q nm ty' <$> regenAbsVars cons
    a :=: b -> do
      a' <- regenAbsVars a 
      b' <- regenAbsVars b 
      return $ a' :=: b'
    a :&: b -> do  
      a' <- regenAbsVars a 
      b' <- regenAbsVars b 
      return $ a' :&: b'
    Top -> return Top
instance RegenAbsVars Spine where  
  regenAbsVars (Abs a ty r) = do
    a' <- getNewWith "@new"
    ty' <- regenAbsVars ty
    r' <- regenAbsVars $ subst (a |-> var a') r
    return $ Abs a' ty' r'
  regenAbsVars (Spine a l) = Spine a <$> mapM regenAbsVars l
 
  
  
