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
import Control.Monad.RWS (RWST, ask, local, censor, runRWST, get, put)
import Control.Monad.Trans.Cont
import Control.Monad.Trans (lift)
import Choice
import Debug.Trace
-----------------------------
---  abstract syntax tree ---
-----------------------------

type Name = String

infixr 0 ~>
(~>) = forall "#"

data Spine = Spine Name [Type]
           | Abs Name Type Spine 
           deriving (Eq)

type Type = Spine
type Term = Spine

data Predicate = Predicate { predName :: Name, predType :: Type, predConstructors :: [(Name,Type)] }
               | Query { predName :: Name, predType ::Spine}
               | Define { predName :: Name, predValue ::Spine, predType :: Type}
               deriving (Eq)


getNewWith s = (++s) <$> getNew

showWithParens t = if (case t of
                          Abs{} -> True
                          Spine "#infer#" _ -> True
                          Spine "#imp_abs#" _ -> True
                          Spine "#forall#" _ -> True
                          Spine "#exists#" _ -> True
                          Spine "#imp_forall#" _ -> True
                          Spine "#ascribe#" _ -> True
                          Spine "#tycon#" _ -> False
                          Spine _ _ -> False
                      ) then "("++show t++")" else show t 

isOperator [] = False
isOperator ('#':l) = False
isOperator (a:l) = not $ elem a ('_':['a'..'z']++['A'..'Z']++['0'..'9'])


instance Show Spine where
  show (Spine "#infer#" [_, Abs nm t t']) = "<"++nm++" : "++show t++"> "++show t'
  show (Spine "#ascribe#" (ty:v:l)) = "( "++showWithParens v++ " : " ++ show ty++" ) "++show (Spine "" l)  
  show (Spine "#forall#" [_,Abs nm t t']) | not (S.member nm $ freeVariables t') = showWithParens t++ " → " ++ show t'
  show (Spine "#imp_forall#" [_,Abs nm t t']) | not (S.member nm $ freeVariables t') = showWithParens t++ " ⇒ " ++ show t'
  show (Spine "#forall#" [_,Abs nm t t']) = "["++nm++" : "++show t++"] "++show t'  
  show (Spine "#imp_forall#" [_,Abs nm t t']) = "{"++nm++" : "++show t++"} "++show t'  
  show (Spine "#tycon#" [Spine nm [t]]) = "{"++nm++" = "++show t++"}"
  show (Spine "#exists#" [_,Abs nm t t']) = "∃ "++nm++" : "++show t++". "++show t' 
  show (Spine "#imp_abs#" [_, Abs nm ty t]) = "?λ "++nm++" : "++showWithParens ty++" . "++show t
  show (Spine nm (t:t':l)) | isOperator nm = "( "++showWithParens t++" "++nm++" "++ show t'++" )"++show (Spine "" l)
  show (Spine h l) = h++concatMap showWithParens' l
     where showWithParens' t = " "++if case t of
                          Abs{} -> True
                          Spine "#tycon#" _ -> False
                          Spine _ lst -> not $ null lst
                      then "("++show t++")" else show t 
  show (Abs nm ty t) = "λ "++nm++" : "++showWithParens ty++" . "++show t

instance Show Predicate where
  show (Predicate nm ty []) = "defn " ++ nm ++ " : " ++ show ty ++ ";"
  show (Predicate nm ty (a:cons)) =
    "defn " ++ nm ++ " : " ++ show ty ++ "\n" ++ "   | " ++ showSingle a ++ concatMap (\x-> "\n   | " ++ showSingle x) cons ++ ";"
      where showSingle (nm,ty) = nm ++ " = " ++ show ty
  show (Query nm val) = "query " ++ nm ++ " = " ++ show val
  show (Define nm val ty) = "defn " ++ nm ++ " : " ++ show ty ++"\n as "++show val
                                               
var nm = Spine nm []
atom = var "atom"
ascribe a t = Spine ("#ascribe#") [t, a]
forall x tyA v = Spine ("#forall#") [tyA, Abs x tyA v]
exists x tyA v = Spine ("#exists#") [tyA, Abs x tyA v]
pack e tau imp tp interface = Spine "pack" [tp, Abs imp tp interface, tau, e]
open cl (imp,ty) (p,iface) cty inexp = Spine "#open#" [cl, ty,Abs imp ty iface, Abs imp ty (Abs p iface cty), Abs imp ty (Abs p iface inexp)] 
infer x tyA v = Spine ("#infer#") [tyA, Abs x tyA v]

imp_forall x tyA v = Spine ("#imp_forall#") [tyA, Abs x tyA v]
imp_abs x tyA v = Spine ("#imp_abs#") [tyA, Abs x tyA v]
tycon nm val = Spine "#tycon#" [Spine nm [val]]
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
rebuildSpine (Spine "#imp_abs#" [ty, Abs nm _ rst]) (a:apps') = case a of 
  -- TODO: this is not right!
  Spine "#tycon#" [Spine nm' [v]] | nm == nm' -> 
      rebuildSpine (subst (nm |-> v) $ rst) apps'

  Spine "#tycon#" [Spine nm' [v]] -> case apps' of
    [] -> rst
    _ -> rebuildSpine (rebuildSpine (imp_abs nm ty $ rst) apps') [a]
  _ -> rebuildSpine rst (a:apps')
  
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
instance Subst Predicate where
  subst sub (Predicate nm ty cons) = Predicate nm (subst sub ty) ((\(nm,t) -> (nm,subst sub t)) <$> cons)
  subst sub (Query nm ty) = Query nm (subst sub ty)
  subst sub (Define nm val ty) = Define nm (subst sub val) (subst sub ty)
  
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

type TypeChecker = ContT Spine (RWST Constants Constraint Integer Choice)

typeCheckToEnv :: TypeChecker Spine -> Env (Spine,Constraint)
typeCheckToEnv m = do
  r <- ask
  s <- get
  (a,s',w) <- lift $ runRWST (runContT m return) r s 
  put s'
  return (a,w)

addToEnv :: (Name -> Spine -> Constraint -> Constraint) -> Name  -> Spine -> TypeChecker a -> TypeChecker a
addToEnv e x ty = mapContT (censor $ e x ty) . liftLocal ask local (M.insert x ty) 
    
  
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
                | Term :@: Type
                | Spine :=: Spine
                | Constraint :&: Constraint
                | Bind Quant Name Type Constraint
                deriving (Eq)
                         
instance Show Constraint where
  show (a :=: b) = show a++" ≐ "++show b
  show (a :@: b) = show a++" ∈ "++show b
  show (a :&: b) = show a++" ∧ "++show b
  show Top = " ⊤ "
  show (Bind q n ty c) = show q++" "++ n++" : "++show ty++" . "++showWithParens c
    where showWithParens Bind{} = show c
          showWithParens _ = "( "++show c++" )"

instance Monoid Constraint where
  mempty = Top
  
  mappend Top b = b
  mappend a Top = a
  mappend (Spine a [] :=: Spine b []) c | a == b = c
  mappend c (Spine a [] :=: Spine b []) | a == b = c
  mappend a b = a :&: b

instance Subst Constraint where
  subst s c = case c of
    Top -> Top
    s1 :@: s2 -> subq (:@:) s1 s2
    s1 :=: s2 -> subq (:=:) s1 s2
    s1 :&: s2 -> subq (:&:) s1 s2
    Bind q nm t c -> Bind q nm' (subst s t) $ subst s' c
      where (nm',s') = newName nm s
    where subq e c1 c2 = e (subst s c1) (subst s c2)
          

(∃) = Bind Exists
(∀) = Bind Forall

class RegenAbsVars a where
  regenAbsVars :: a -> Env a
instance RegenAbsVars Constraint where  
  regenAbsVars cons = case cons of
    Bind q nm ty cons -> do
      ty' <- regenAbsVars ty
      case nm of
        "" -> do
          nm' <- getNewWith "@newer"
          let sub = nm |-> var nm'
          Bind q nm' ty' <$> regenAbsVars (subst sub cons)
        _ -> Bind q nm ty' <$> regenAbsVars cons
    Spine a [] :=: Spine b [] | a == b -> return Top
    a :=: b -> regen (:=:) a b
    a :&: b -> regen (:&:) a b
    a :@: b -> regen (:@:) a b
    Top -> return Top
    where regen e a b = do
            a' <- regenAbsVars a 
            b' <- regenAbsVars b 
            return $ e a' b'
instance RegenAbsVars Spine where  
  regenAbsVars (Abs a ty r) = do
    a' <- getNewWith "@new"
    ty' <- regenAbsVars ty
    r' <- regenAbsVars $ subst (a |-> var a') r
    return $ Abs a' ty' r'
  regenAbsVars (Spine a l) = Spine a <$> mapM regenAbsVars l
 
getFamily (Spine "#infer#" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#ascribe#"  (_:v:l)) = getFamily v
getFamily (Spine "#forall#" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#imp_forall#" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#exists#" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#open#" (_:_:_:_:Abs _ _ (Abs _ _ c):_)) = getFamily c
getFamily (Spine nm' _) = nm'
getFamily v = error $ "values don't have families: "++show v


consts = [ ("atom", atom)
         , ("#ascribe#", forall "a" atom $ (var "a") ~> (var "a"))
         , ("#infer#", forall "a" atom $ (var "a" ~> atom) ~> atom)
         , ("#forall#", forall "a" atom $ (var "a" ~> atom) ~> atom)
         , ("#imp_forall#", forall "a" atom $ (var "a" ~> atom) ~> atom)
         , ("#imp_abs#", forall "a" atom $ forall "foo" (var "a" ~> atom) $ imp_forall "z" (var "a") (Spine "foo" [var "z"]))
         , ("#exists#", forall "a" atom $ (var "a" ~> atom) ~> atom)
         , ("pack", forall "tp" atom 
                  $ forall "iface" (var "tp" ~> atom) 
                  $ forall "tau" (var "tp") 
                  $ forall "e" (Spine "iface" [var "tau"]) 
                  $ exists "z" (var "tp") (Spine "iface" [var "z"]))
         ]

envConsts = M.fromList consts