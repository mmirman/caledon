{-# LANGUAGE
 FlexibleInstances,
 PatternGuards,
 BangPatterns,
 FlexibleContexts,
 TupleSections
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
(~>) = forall ""
(~~>) = imp_forall ""

data Spine = Spine Name [Type]
           | Abs Name Type Spine 
           deriving (Eq)

type Type = Spine
type Term = Spine

data Predicate = Predicate { predIsSound :: !Bool, predName :: !Name, predType :: !Type, predConstructors :: ![(Bool,(Name,Type))] }
               | Query { predName :: !Name, predType :: !Spine}
               | Define { predIsSound :: !Bool, predName :: !Name, predValue :: !Spine, predType :: !Type}
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
  return $ show n
  
getNewWith :: (Functor f, MonadState c f, ValueTracker c) => String -> f String
getNewWith s = {- (++s) <$> -} getNew

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
  show (Spine nm l@[_ , Abs _ _ _]) | isOperator nm = "("++nm++") "++show (Spine "" l)
  show (Spine nm (t:t':l)) | isOperator nm = "( "++showWithParens t++" "++nm++" "++ show t'++" )"++show (Spine "" l)
  show (Spine h l) = h++concatMap showWithParens' l
     where showWithParens' t = " "++if case t of
                          Abs{} -> True
                          Spine "#tycon#" _ -> False
                          Spine _ lst -> not $ null lst
                      then "("++show t++")" else show t 
  show (Abs nm ty t) = "λ "++nm++" : "++showWithParens ty++" . "++show t

showT True = "defn "
showT False = "unsound "

instance Show Predicate where
  show (Predicate s nm ty []) = showT s ++ nm ++ " : " ++ show ty
  show (Predicate s nm ty (a:cons)) =
    showT s++ nm ++ " : " ++ show ty++showSingle a ++ concatMap (\x-> showSingle x) cons
      where showSingle (b,(nm,ty)) = (if b then "\n   >| " else "   | ") ++nm ++ " = " ++ show ty
  show (Query nm val) = "query " ++ nm ++ " = " ++ show val
  show (Define s nm val ty) = showT s ++ nm ++ " : " ++ show ty ++"\n as "++show val
                                               
var !nm = Spine nm []
atomName = "prop"
tipeName = "type"
kindName = "#kind#"

atom = var atomName
tipe = var tipeName
kind = var kindName  -- can be either a type or an atom
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
  Nothing -> seq sp $ if ty == atom && S.notMember nm (freeVariables rs) then rs else irs 
                      -- proof irrelevance hack
                      -- we know we can prove that type "prop" is inhabited
                      -- irs - the proof doesn't matter
                      -- rs - the proof matters
                      -- irs - here, the proof might matter, but we don't know if we can prove the thing, 
                      -- so we need to try
     where nm' = newNameFor nm $ freeVariables apps
           sp = subst (nm |-> var nm') rst
           rs = rebuildSpine sp apps
           irs = infer nm ty rs
rebuildSpine (Spine c apps) apps' = Spine c $ apps ++ apps'
rebuildSpine (Abs nm _ rst) (a:apps') = let sp = subst (nm |-> a) $ rst
                                        in seq sp $ rebuildSpine sp apps'

newNameFor :: Name -> S.Set Name -> Name
newNameFor nm fv = nm'
  where nm' = fromJust $ find free $ nm:map (\s -> show s ++ "/?") [0..]
        free k = not $ S.member k fv
        
newName :: Name -> Map Name Spine -> S.Set Name -> (Name, Map Name Spine, S.Set Name)
newName "" so fo = ("",so,fo)
newName nm so fo = (nm',s',f')
  where s = M.delete nm so  
        -- could reduce the size of the free variable set here, but for efficiency it is not really necessary
        -- for beautification of output it is
        (s',f') = if nm == nm' then (s,fo) else (M.insert nm (var nm') s , S.insert nm' fo)
        nm' = fromJust $ find free $ nm:map (\s -> show s ++ "/") [0..]
        fv = mappend (M.keysSet s) (freeVariables s)
        free k = not $ S.member k fv

class Subst a where
  substFree :: Substitution -> S.Set Name -> a -> a
  
subst s = substFree s $ freeVariables s

class Alpha a where  
  alphaConvert :: S.Set Name -> a -> a
  rebuildFromMem :: Map Name Name -> a -> a  
  
instance Subst a => Subst [a] where
  substFree s f t = substFree s f <$> t
  
instance Alpha a => Alpha [a] where  
  alphaConvert s l = alphaConvert s <$> l
  rebuildFromMem s l = rebuildFromMem s <$> l
  
instance (Subst a, Subst b) => Subst (a,b) where
  substFree s f ~(a,b) = (substFree s f a , substFree s f b)
  
instance Subst Spine where
  substFree s f sp@(Spine "#imp_forall#" [_, Abs nm tp rst]) = case "" /= nm && S.member nm f && not (S.null $ S.intersection (M.keysSet s) $ freeVariables sp) of
    False -> imp_forall nm (substFree s f tp) $ substFree (M.delete nm s) f rst
    True -> error $ 
            "can not capture free variables because implicits quantifiers can not alpha convert: "++ show sp 
            ++ "\n\tfor: "++show s
  substFree s f sp@(Spine "#imp_abs#" [_, Abs nm tp rst]) = case "" /= nm && S.member nm f && not (S.null $ S.intersection (M.keysSet s) $ freeVariables sp) of
    False  -> imp_abs nm (substFree s f tp) $ substFree (M.delete nm s) f rst 
    True   -> error $ 
              "can not capture free variables because implicit binds can not alpha convert: "++ show sp
              ++ "\n\tfor: "++show s
  substFree s f (Abs nm tp rst) = Abs nm' (substFree s f tp) $ substFree s' f' rst
    where (nm',s',f') = newName nm s f
  substFree s f (Spine "#tycon#" [Spine c [v]]) = Spine "#tycon#" [Spine c [substFree s f v]]
  substFree s f (Spine nm apps) = let apps' = substFree s f <$> apps  in
    case s ! nm of
      Just nm -> rebuildSpine nm apps'
      _ -> Spine nm apps'
      
instance Alpha Spine where
  alphaConvert s (Spine "#imp_forall#" [_,Abs a ty r]) = imp_forall a ty $ alphaConvert (S.insert a s) r
  alphaConvert s (Spine "#imp_abs#" [_,Abs a ty r]) = imp_abs a ty $ alphaConvert (S.insert a s) r
  alphaConvert s (Abs nm ty r) = Abs nm' (alphaConvert s ty) $ alphaConvert (S.insert nm' s) r
    where nm' = newNameFor nm s
  alphaConvert s (Spine a l) = Spine a $ alphaConvert s l
  
  rebuildFromMem s (Spine "#imp_forall#" [_,Abs a ty r]) = imp_forall a (rebuildFromMem s ty) $ rebuildFromMem (M.delete a s) r
  rebuildFromMem s (Spine "#imp_abs#" [_,Abs a ty r]) = imp_abs a (rebuildFromMem s ty) $ rebuildFromMem (M.delete a s) r
  rebuildFromMem s (Abs nm ty r) = Abs (fromMaybe nm $ M.lookup nm s) (rebuildFromMem s ty) $ rebuildFromMem s r
  rebuildFromMem s (Spine a l) = Spine a' $ rebuildFromMem s l
    where a' = fromMaybe a $ M.lookup a s
                                 
  
instance Subst Predicate where
  substFree sub f (Predicate s nm ty cons) = Predicate s nm (substFree sub f ty) ((\(b,(nm,t)) -> (b,(nm,substFree sub f t))) <$> cons)
  substFree sub f (Query nm ty) = Query nm (substFree sub f ty)
  substFree sub f (Define s nm val ty) = Define s nm (substFree sub f val) (substFree sub f ty)
  
class FV a where         
  freeVariables :: a -> S.Set Name
instance (FV a, F.Foldable f) => FV (f a) where
  freeVariables m = F.foldMap freeVariables m
instance FV Spine where
  freeVariables t = case t of
    Abs nm t p -> (S.delete nm $ freeVariables p) `mappend` freeVariables t
    Spine "#tycon#" [Spine nm [v]] -> freeVariables v
    Spine ['\'',_,'\''] [] -> mempty
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
  substFree s f c = case c of
    s1 :@: s2 -> subq s f (:@:) s1 s2
    s1 :=: s2 -> subq s f (:=:) s1 s2
    
instance Subst Constraint where
  substFree s f c = case c of
    SCons l -> SCons $ map (substFree s f) l
    s1 :&: s2 -> subq s f (:&:) s1 s2
    Bind q nm t c -> Bind q nm' (substFree s f t) $ substFree s' f' c
      where (nm',s',f') = newName nm s f
            
subq s f e c1 c2 = e (substFree s f c1) (substFree s f c2)

(∃) = Bind Exists
(∀) = Bind Forall
  
infixr 0 <<$>
(<<$>) f m = ( \(a,b) -> (f a, b)) <$> m

regenM e a b = do
  (a',s1) <- regenWithMem a 
  (b',s2) <- regenWithMem b 
  return $ (e a' b', M.union s1 s2)
regen e a b = do
  a' <- regenAbsVars a 
  b' <- regenAbsVars b 
  return $ e a' b'  
  
class RegenAbsVars a where
  regenAbsVars :: (Functor f, MonadState c f, ValueTracker c) => a -> f a
  regenWithMem :: (Functor f, MonadState c f, ValueTracker c) => a -> f (a, Map Name Name)
  
instance RegenAbsVars l => RegenAbsVars [l] where
  regenAbsVars cons = mapM regenAbsVars cons
  
  regenWithMem cons = together <$> mapM regenWithMem cons
    where together f = (l',foldr M.union mempty ss)
            where (l',ss) = unzip f
  

  
instance RegenAbsVars Spine where  
  regenAbsVars (Spine "#imp_forall#" [_,Abs a ty r]) = imp_forall a ty <$> regenAbsVars r
  regenAbsVars (Spine "#imp_abs#" [_,Abs a ty r]) = imp_abs a ty <$> regenAbsVars r
  regenAbsVars (Abs a ty r) = do
    a' <- getNewWith $ "@rega"
    ty' <- regenAbsVars ty
    r' <- regenAbsVars $ subst (a |-> var a') r
    return $ Abs a' ty' r'
  regenAbsVars (Spine a l) = Spine a <$> regenAbsVars l
  
  regenWithMem (Spine "#imp_forall#" [_,Abs a ty r]) = imp_forall a ty <<$> regenWithMem r
  regenWithMem (Spine "#imp_abs#" [_,Abs a ty r]) = imp_abs a ty <<$> regenWithMem r
  regenWithMem (Abs a ty r) = do
    a' <- getNewWith $ "@regm"
    (ty',s1) <- regenWithMem ty
    (r', s2) <- regenWithMem $ subst (a |-> var a') r
    return $ (Abs a' ty' r', M.insert a' a $ M.union s1 s2)
  regenWithMem (Spine a l) = Spine a <<$> regenWithMem l



instance RegenAbsVars SCons where
  regenAbsVars cons = case cons of
    a :=: b -> regen (:=:) a b
    a :@: b -> regen (:@:) a b
    
  regenWithMem cons = case cons of
    a :=: b -> regenM (:=:) a b
    a :@: b -> regenM (:@:) a b    
      
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
    
  regenWithMem cons = case cons of
    Bind q nm ty cons -> do
      (ty',s1) <- regenWithMem ty
      nm' <- getNewWith "@regm'"
      let sub = nm |-> var nm'
      (cons',s2) <- regenWithMem $ subst sub cons
      return (Bind q nm' ty' cons', M.insert nm' nm $ M.union s1 s2)
    SCons l -> SCons <<$> regenWithMem l
    a :&: b -> regenM (:&:) a b    
  
getFamily (Spine "#infer#" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#ascribe#"  (_:v:l)) = getFamily (rebuildSpine v l)
getFamily (Spine "#forall#" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#imp_forall#" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#exists#" [_, Abs _ _ lm]) = getFamily lm
getFamily (Spine "#open#" (_:_:c:_)) = getFamily c
getFamily (Spine "open" (_:_:c:_)) = getFamily c
getFamily (Spine "pack" [_,_,_,e]) = getFamily e
getFamily (Spine nm' _) = nm'
getFamily v = error $ "values don't have families: "++show v


consts = [ (atomName , tipe)
         , (tipeName , kind)
         , (kindName , kind)
         -- atom : kind
           
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


anonymous ty = ((False,100),ty)

envSet = S.fromList $ map fst consts

toNCCchar c = Spine ['\'',c,'\''] []
toNCCstring s = foldr cons nil $ map toNCCchar s
  where char = Spine "char" []
        nil = Spine "nil" [tycon "a" char]
        cons a l = Spine "cons" [tycon "a" char, a,l]

envConsts = anonymous <$> M.fromList consts

isChar  ['\'',_,'\''] = True
isChar _ = False
