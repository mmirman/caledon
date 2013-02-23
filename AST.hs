{-# LANGUAGE
 DeriveFunctor,
 FlexibleInstances,
 PatternGuards,
 BangPatterns,
 FlexibleContexts
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
import Control.Monad.RWS (RWST)
import Control.Monad.State.Class (MonadState(), get, modify)

import Choice

-----------------------------
---  abstract syntax tree ---
-----------------------------

type Name = String

infixr 0 ~>
infixr 0 ~~>
(~>) = forall "#"
(~~>) = imp_forall "#"

data Spine = Spine !Name ![Type]
           | Abs !Name !Type !Spine 
           deriving (Eq)

type Type = Spine
type Term = Spine

data Predicate = Predicate { predName :: !Name, predType :: !Type, predConstructors :: ![(Name,(Bool,Type))] }
               | Query { predName :: !Name, predType :: !Spine}
               | Define { predName :: !Name, predValue :: !Spine, predType :: !Type}
               deriving (Eq)

class ValueTracker c where
  putValue :: Integer -> c -> c
  takeValue :: c -> Integer

instance ValueTracker Integer where
  putValue _ i = i
  takeValue i = i

getNew :: (Functor m, MonadState c m, ValueTracker c) => m String
getNew = do
  st <- takeValue <$> get
  let n = 1 + st
  modify $ putValue n
  return $! show n
  
getNewWith :: (Functor f, MonadState c f, ValueTracker c) => String -> f String
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
isOperator ('#':_) = False
isOperator (a:_) = not $ elem a ('_':['a'..'z']++['A'..'Z']++['0'..'9'])


instance Show Spine where
  show (Spine ['\'',c,'\''] []) = show c
  show (Spine "#infer#" [_, Abs nm t t']) = "<"++nm++" : "++show t++"> "++show t'
  show (Spine "#ascribe#" (ty:v:l)) = "( "++showWithParens v++ " : " ++ show ty++" ) "++show (Spine "" l)  
  show (Spine "#forall#" [_,Abs nm t t']) | not (S.member nm $ freeVariables t') = showWithParens t++ " → " ++ show t'
  show (Spine "#imp_forall#" [_,Abs nm t t']) | not (S.member nm $ freeVariables t') = showWithParens t++ " ⇒ " ++ show t'
  show (Spine "#forall#" [_,Abs nm t t']) = "["++nm++" : "++show t++"] "++show t'  
  show (Spine "#imp_forall#" [_,Abs nm t t']) = "{"++nm++" : "++show t++"} "++show t'  
  show (Spine "#tycon#" [Spine nm [t]]) = "{"++nm++" = "++show t++"}"
  show (Spine "#exists#" [_,Abs nm t t']) = "∃ "++nm++" : "++show t++". "++show t' 
  show (Spine "#imp_abs#" [_,Abs nm ty t]) = "?λ "++nm++" : "++showWithParens ty++" . "++show t
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
      where showSingle (nm,ty) = nm ++ " = " ++ show (snd ty)
  show (Query nm val) = "query " ++ nm ++ " = " ++ show val
  show (Define nm val ty) = "defn " ++ nm ++ " : " ++ show ty ++"\n as "++show val
                                               
var !nm = Spine nm []
atom = var "atom"
ascribe !a !t = Spine ("#ascribe#") [t, a]
forall !x !tyA !v = Spine ("#forall#") [tyA, Abs x tyA v]
exists !x !tyA !v = Spine ("#exists#") [tyA, Abs x tyA v]
pack !e !tau !imp !tp !interface = Spine "pack" [tp, Abs imp tp interface, tau, e]
open !cl (!imp,!ty) (!p,!iface) !cty !inexp = Spine "#open#" [cl, ty,Abs imp ty iface, Abs imp ty (Abs p iface cty), Abs imp ty (Abs p iface inexp)] 
infer !x !tyA !v = Spine ("#infer#") [tyA, Abs x tyA v]

imp_forall !x !tyA !v = Spine ("#imp_forall#") [tyA, Abs x tyA v]
imp_abs !x !tyA !v = Spine ("#imp_abs#") [tyA, Abs x tyA v]
tycon !nm !val = Spine "#tycon#" [Spine nm [val]]
---------------------
---  substitution ---
---------------------

type Substitution = M.Map Name Spine

infixr 1 |->
infixr 0 ***
m1 *** m2 = M.union m2 $ subst m2 <$> m1
(|->) = M.singleton
(!) = flip M.lookup


findTyconInPrefix nm = fip []
  where fip l (Spine "#tycon#" [Spine nm' [v]]:r) | nm == nm' = Just (v, reverse l++r)
        fip l (a@(Spine "#tycon#" [Spine _ [_]]):r) = fip (a:l) r
        fip _ _ = Nothing

apply :: Spine -> Spine -> Spine
apply !a !l = rebuildSpine a [l]

rebuildSpine :: Spine -> [Spine] -> Spine
rebuildSpine s [] = s
rebuildSpine (Spine "#imp_abs#" [_, Abs nm ty rst]) apps = case findTyconInPrefix nm apps of 
  Just (v, apps) -> rebuildSpine (Abs nm ty rst) (v:apps)
  Nothing -> seq sp $ infer nm ty $ rebuildSpine sp apps
     where nm' = newNameFor nm $ freeVariables apps
           sp = subst (nm |-> var nm') rst
rebuildSpine (Spine c apps) apps' = Spine c $ apps ++ apps'
rebuildSpine (Abs nm _ rst) (a:apps') = let sp = subst (nm |-> a) $ rst
                                        in seq sp $ rebuildSpine sp apps'

newNameFor :: Name -> S.Set Name -> Name
newNameFor nm fv = nm'
  where nm' = fromJust $ find free $ nm:map (\s -> show s ++ "/?") [0..]
        free k = not $ S.member k fv
        
newName :: Name -> Map Name Spine -> (Name, Map Name Spine)
newName nm so = (nm',s')
  where s = M.delete nm so
        s' = if nm == nm' then s else M.insert nm (var nm') s 
        nm' = fromJust $ find free $ nm:map (\s -> show s ++ "/") [0..]
        fv = mappend (M.keysSet s) (freeVariables s)
        free k = not $ S.member k fv

class Subst a where
  subst :: Substitution -> a -> a
instance Subst a => Subst [a] where
  subst foo !t = subst foo <$> t
instance (Subst a, Subst b) => Subst (a,b) where
  subst foo (!a,!b) = (subst foo a , subst foo b)
instance Subst Spine where
  subst s (Abs !nm !tp !rst) = Abs nm' (subst s tp) $ subst s' rst
    where (nm',s') = newName nm s
  subst s (Spine "#tycon#" [Spine c [!v]]) = Spine "#tycon#" [Spine c [subst s v]]
  subst s (Spine !nm !apps) = let apps' = subst s <$> apps  in
    case s ! nm of
      Just nm -> rebuildSpine nm apps'
      _ -> Spine nm apps'
instance Subst Predicate where
  subst sub (Predicate nm ty cons) = Predicate nm (subst sub ty) ((\(nm,(b,t)) -> (nm,(b,subst sub t))) <$> cons)
  subst sub (Query nm ty) = Query nm (subst sub ty)
  subst sub (Define nm val ty) = Define nm (subst sub val) (subst sub ty)
  
class FV a where         
  freeVariables :: a -> S.Set Name
instance (FV a, F.Foldable f) => FV (f a) where
  freeVariables m = F.foldMap freeVariables m
instance FV Spine where
  freeVariables t = case t of
    Abs nm t p -> (S.delete nm $ freeVariables p) `mappend` freeVariables t
    Spine "#tycon#" [Spine nm [v]] -> freeVariables v
    Spine head others -> mappend (S.singleton head) $ mconcat $ map freeVariables others


  
-------------------------
---  Constraint types ---
-------------------------

data Quant = Forall | Exists deriving (Eq) 

instance Show Quant where
  show Forall = "∀"
  show Exists = "∃"

-- as ineficient as it is, I'll make this the constraint representation.
infix 2 :=:  
infix 2 :@:  
infixr 1 :&:

-- we can make this data structure mostly strict since the only time we don't 
-- traverse it is when we fail, and in order to fail, we always have to traverse
-- the lhs!
data SCons = !Term :@: !Type
           | !Spine :=: !Spine
           deriving (Eq)
data Constraint = SCons [SCons]
                  -- we don't necessarily have to traverse the rhs of a combination
                  -- so we can make it lazy
                | !Constraint :&: Constraint 
                | Bind !Quant !Name !Type !Constraint
                deriving (Eq)
                         
instance Show SCons where
  show (a :=: b) = show a++" ≐ "++show b
  show (a :@: b) = show a++" ∈ "++show b
  
instance Show Constraint where
  show (SCons []) = " ⊤ "
  show (SCons l) = concat $ intersperse " ∧ " $ map show l
  show (a :&: b) = show a++" ∧ "++show b
  
  show (Bind q n ty c) = show q++" "++ n++" : "++show ty++" . "++showWithParens c
    where showWithParens Bind{} = show c
          showWithParens _ = "( "++show c++" )"

instance Monoid Constraint where
  mempty = SCons []
  
  mappend (SCons []) b = b

  mappend a (SCons []) = a
  mappend (SCons a) (SCons b) = SCons $ a++b
  mappend a b = a :&: b

{-# RULES
 "mappendmempty" mappend mempty = id
 #-}

{-# RULES
 "memptymappend" flip mappend mempty = id
 #-}

instance Subst SCons where
  subst s c = case c of
    s1 :@: s2 -> subq s (:@:) s1 s2
    s1 :=: s2 -> subq s (:=:) s1 s2    
instance Subst Constraint where
  subst s c = case c of
    SCons l -> SCons $ map (subst s) l
    s1 :&: s2 -> subq s (:&:) s1 s2
    Bind q nm t c -> Bind q nm' (subst s t) $ subst s' c
      where (nm',s') = newName nm s

subq s e c1 c2 = e (subst s c1) (subst s c2)

(∃) = Bind Exists
(∀) = Bind Forall

class RegenAbsVars a where
  regenAbsVars :: (Functor f, MonadState c f, ValueTracker c) => a -> f a
  
instance RegenAbsVars SCons where
  regenAbsVars cons = case cons of
    a :=: b -> regen (:=:) a b
    a :@: b -> regen (:@:) a b
    
instance RegenAbsVars [SCons] where
  regenAbsVars cons = mapM regenAbsVars cons    
    
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
    SCons l -> SCons <$> regenAbsVars l
    a :&: b -> regen (:&:) a b


regen e a b = do
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
getFamily (Spine "#ascribe#"  (_:v:_)) = getFamily v
getFamily (Spine "#forall#" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#imp_forall#" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#exists#" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#open#" (_:_:c:_)) = getFamily c
getFamily (Spine "open" (_:_:c:_)) = getFamily c
getFamily (Spine "pack" [_,_,_,e]) = getFamily e
getFamily (Spine nm' _) = nm'
getFamily v = error $ "values don't have families: "++show v


consts = [ ("atom", atom)
         , ("#ascribe#", forall "a" atom $ (var "a") ~> (var "a"))
         , ("#forall#", forall "a" atom $ (var "a" ~> atom) ~> atom)
         , ("#imp_forall#", forall "a" atom $ (var "a" ~> atom) ~> atom)
         , ("#imp_abs#", forall "a" atom $ forall "foo" (var "a" ~> atom) $ imp_forall "z" (var "a") (Spine "foo" [var "z"]))
         , ("#exists#", forall "a" atom $ (var "a" ~> atom) ~> atom)
         , ("pack", forall "tp" atom 
                  $ forall "iface" (var "tp" ~> atom) 
                  $ forall "tau" (var "tp") 
                  $ forall "e" (Spine "iface" [var "tau"]) 
                  $ exists "z" (var "tp") (Spine "iface" [var "z"]))
         , ("open", forall "a" atom 
                  $ forall "f" (var "a" ~> atom) 
                  $ exists "z" (var "a") (Spine "f" [var "z"])
                  ~> (forall "v" (var "a") 
                     $ Spine "f" [var "v"] ~> atom ))
         , ("openDef", forall "a" atom 
                    $ forall "f" (var "a" ~> atom) 
                    $ forall "v" (var "a")
                    $ forall "fv" (Spine "f" [var "z"])
                    $ Spine "open" [var "a",  var "f", Spine "pack" [var "a", var "f", var "v", var "fv"] , var "v", var "fv"])
         ]

toNCCchar c = Spine ['\'',c,'\''] []
toNCCstring s = foldr cons nil $ map toNCCchar s
  where char = Spine "char" []
        nil = Spine "nil" [tycon "a" char]
        cons a l = Spine "cons" [tycon "a" char, a,l]

envConsts = M.fromList consts

isChar  ['\'',l,'\''] = True
isChar _ = False



