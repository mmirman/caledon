{-# LANGUAGE 
 ViewPatterns,
 BangPatterns
 #-}
module Src.Substitution where

import Src.Tracing
import Src.AST
import Src.Context
import Data.Functor

import qualified Data.Set as S  
import qualified Data.Map as M
import Data.Monoid

type Foralls = [Type]

liftThree i (a,b,DeBr c) = (liftV i a, liftV i b, DeBr $ i + c)
liftThree i (a,b,Exi j n t) = (liftV i a, liftV i b, Exi j n $ liftV i t)
liftThree i (a,b,c) = (liftV i a, liftV i b, c)

etaExpand :: Type -> P -> N
etaExpand (viewForallP -> Just ~(a,_)) m = 
  -- only eta expand heads and not arguments since we need arguments in eta reduced form for type checking!
  Abs a $ Pat $ (liftV 1 m) :+: var 0 -- etaExpand (liftV 1 a) (vvar 0)
etaExpand _ m = Pat m

substN :: Context c => Bool -> c -> (Term,Type, Variable) -> N -> N
substN t ctxt na (Pat p) = case substP t ctxt na p of
  (Right m,_) -> m
  (Left  m,p) -> if t then etaExpand p m else Pat m
substN t ctxt na (Abs b n) = 
  -- don't bother eta-expanding types, just patterns
  Abs (substTy ctxt na b) $ substN t (putTy ctxt b) (liftThree 1 na) n

substP :: Context c => Bool -> c -> (Term,Type, Variable) -> P -> (Either P N, Type)
substP _ _ sub@(n, a, Exi i nm _) targ@(Var (Exi i' nm' _)) | nm == nm' = 
  if i == i' 
  then (Right n, a) 
  else error $ "these should be the same depth! ["++show sub++"] "++show targ
substP _ _ (n, a, x') (Var x) | x == x' = (Right n, a)
substP _ ctxt na (Var (Exi i nm ty)) = (Left $ Var $ Exi i nm ty', ty')
  where ty' = substTy ctxt na ty
substP _ ctxt _ (y@(Var v)) = (Left y, getTy ctxt v)
substP t ctxt na (p :+: n) = hered t ctxt (substP t ctxt na p) (substNnoEta t ctxt na n)

hered :: Context c => Bool -> c -> (Either P N, Type) -> N -> (Either P N, Type)
hered t ctxt (Right p1@(Abs a1 n), l) nv = 
  ( Right $ liftV (-1) $ substN t (putTy ctxt a1) (liftV 1 nv,liftV 1 a1,DeBr 0) n
  , case viewForallP l of 
    Just ~(a1',a2) -> liftV (-1) $ substTy (putTy ctxt a1') (liftV 1 nv,liftV 1 a1',DeBr 0) a2
    Nothing -> error $ show p1++" r: "++show l
  )  
hered t ctxt (Right (Pat p1), l) nv = case hered t ctxt (Left p1,l) nv of
  (Left p , l) -> (Right $ Pat p, l)
  (Right p, l) -> (Right p, l)
hered _ ctxt (Left p1, l) nv = 
  ( Left $ p1 :+: nv
  , case viewForallP l of
    Just ~(a1',a2) -> liftV (-1) $ substTy (putTy ctxt a1') (liftV 1 nv, liftV 1 a1',DeBr 0) a2
    Nothing -> case (p1, nv) of
      (Var (Con "type"), Pat n) | isUniverse n -> p1 :+: nv
      _ -> error $ show p1++" l: "
           ++show l
           ++"\n :+: "++show nv 
           ++"\n CTXT: "++show ctxt
           ++ "\nFROM SUBSTITUTION "
  )
  

substTy c (a,_,s) t = fromType $ substP' (a,s) t

substNnoEta b c (a,_,s) t = substN' (a,s) t

substituteType :: (Term, Type, Variable) -> P -> P
substituteType = substTy ()

substF :: Context c => c -> (Term,Type,Variable) -> Form -> Form  
substF _ _ Done = Done
substF ctxt sub (a :=: b) = substN True ctxt sub a :=: substN True ctxt sub b
substF ctxt sub (a :<: b) = substN True ctxt sub a :<: substN True ctxt sub b
substF ctxt sub (a :<=: b) = substN True ctxt sub a :<=: substN True ctxt sub b

substF ctxt sub (a :@: b) = substN True ctxt sub a :@: substTy ctxt sub b
substF ctxt sub (a :&: b) = substF ctxt sub a :&: substF ctxt sub b
substF ctxt sub (Bind ty f) = Bind (substTy ctxt sub ty) $ substF (putTy ctxt ty) (liftThree 1 sub) f

subst c s f = substF c s f

app  :: Context c => c -> Either P N -> N -> Either P N
app ctxt (Right (Abs a1 n)) nv = Right $ liftV (-1) $ substN True (putTy ctxt a1) (liftV 1 nv,liftV 1 a1,DeBr 0) n
app _ (Right (Pat p1)) nv = Right $ Pat (p1 :+: nv)
app _ (Left p1) nv = Left $ p1 :+: nv

app'  :: Either P N -> N -> Either P N
app' (Right (Abs a1 n)) nv = Right $ liftV (-1) $ substN' (liftV 1 nv,DeBr 0) n
app' (Right (Pat p1)) nv = Right $ Pat (p1 :+: nv)
app' (Left p1) nv = Left $ p1 :+: nv

appP :: Context c => c -> N -> P -> N
appP c p n = case app c (Right p) (Pat n) of
  Right n -> n
  Left p -> Pat p

appN :: Context c => c -> N -> N -> N
appN c p n = case app c (Right p) n of
  Right n -> n
  Left p -> Pat p

appP' :: N -> P -> N
appP' p n = case app' (Right p) (Pat n) of
  Right n -> n
  Left p -> Pat p
  
appN' :: N -> N -> N
appN' p n = case app' (Right p) n of
  Right n -> n
  Left p -> Pat p

freeVarsN (Pat p) = freeVarsP p
freeVarsN (Abs t1 t2) = freeVarsP t1 `mappend` freeVarsN t2

freeVarsP (Var (Exi j nm t)) = M.insert nm j $ freeVarsP t
freeVarsP (Var _) = mempty
freeVarsP (p :+: n) = freeVarsP p `mappend` freeVarsN n

freeVarsMapN (Pat p) = freeVarsMapP p
freeVarsMapN (Abs t1 t2) = freeVarsMapP t1 `mappend` freeVarsMapN t2

freeVarsMapP (Var (Exi depth nm t)) = M.insert nm (depth,t) $ freeVarsMapP t
freeVarsMapP (Var _) = mempty
freeVarsMapP (p :+: n) = freeVarsMapP p `mappend` freeVarsMapN n


containsN i (Pat p) = containsP i p
containsN i (Abs t1 t2) = containsP i t1 || containsN (i+1) t2

containsP i (Var v) = case v of
  Exi _ _ t -> containsP i t
  DeBr j -> i == j
  _ -> False
containsP i (p :+: n) = containsP i p || containsN i n


etaReduce (Abs ty n) = case etaReduce n of
  Pat (a :+: b) -> case etaReduce b of
    b'@(Pat (Var (DeBr 0))) -> if containsP 0 a 
                               then Abs ty $ Pat $ a :+: b'
                               else Pat $ liftV (-1) a
    b' -> Abs ty $ Pat $ a :+: b'
  n -> Abs ty n
etaReduce p = p














liftTwo i (a,DeBr c) = (liftV i a, DeBr $ i + c)
liftTwo i (a,Exi j n t) = (liftV i a, Exi j n $ liftV i t)
liftTwo i (a,c) = (liftV i a, c)

substN' :: (Term, Variable) -> N -> N
substN' na (Pat p) = substP' na p
substN' na (Abs b n) = Abs (fromType $ substP' na b) $ substN' (liftTwo 1 na) n
  
substP' :: (Term,Variable) -> P -> N
substP' sub@(n, Exi i nm _) targ@(Var (Exi i' nm' _)) | nm == nm' = 
  if i == i' 
  then n
  else error $ nm++" and "++nm'++" should be the same depth! ["++show sub++"] "++show targ
substP' (n, x') (Var x) | x == x' = n
substP' na (Var (Exi i nm ty)) = Pat $ Var $ Exi i nm $ fromType $ substP' na ty
substP' _ (y@(Var v)) = Pat y
substP' na (p :+: n) = hered' (substP' na p) (substN' na n)
  

hered' :: N -> N -> N
hered' p1@(Abs a1 n) nv = liftV (-1) $ substN'  (liftV 1 nv,DeBr 0) n
hered' (Pat p1) nv = Pat $ p1 :+: nv


substF' :: (Term,Variable) -> Form -> Form  
substF' _ Done = Done
substF' sub (a :=: b) = substN' sub a :=: substN' sub b
substF' sub (a :<: b) = substN' sub a :<: substN' sub b
substF' sub (a :<=: b) = substN' sub a :<=: substN' sub b

substF' sub (a :@: b) = substN' sub a :@: fromType (substP' sub b)
substF' sub (a :&: b) = substF' sub a :&: substF' sub b
substF' sub (Bind ty f) = Bind (fromType $ substP' sub ty) $ substF' (liftTwo 1 sub) f

subst' s f = substF' s f

infinity = 100000000000000000000

maybeMin (Just a) (Just b) = Just $ min a b
maybeMin Nothing b = b
maybeMin a Nothing = a



class CheckExi a where
  checkExi :: Int -> a -> Bool
  
  minFreeVars :: Int -> Int -> a -> Maybe Int
  
instance CheckExi Variable where
  minFreeVars c j (Exi a nm ty) = (if c - a + 1 > j then Just $ c - a - j + 1 else Nothing) `maybeMin` minFreeVars c j ty
  minFreeVars c j (DeBr i) | i < 0 = error $ "CAN NOT HAVE NEGATIVE VARS: "++show i
  minFreeVars c j (DeBr i) = if i > j then Just (i - j) else Nothing
  minFreeVars _ _ (Con _) = Nothing
  
  checkExi i e@(Exi a nm ty) = case minFreeVars i 0 ty of
    Nothing -> checkExi i ty 
    Just v | i - a <= v -> checkExi i ty 
    Just v -> error $ "OUT OF SCOPE "++show v++" IN: "++show e
  checkExi i _ = True

instance CheckExi P where
  minFreeVars c i (a :+: b) = minFreeVars c i a `maybeMin` minFreeVars c i b 
  minFreeVars c  i (Var a) = minFreeVars c i a
  
  checkExi i (a :+: b) = checkExi i a && checkExi i b
  checkExi i (Var v) = checkExi i v
  
instance CheckExi N where
  minFreeVars c i (Abs ty b) = minFreeVars c i ty `maybeMin` minFreeVars (c + 1) (i+1) b 
  minFreeVars c i (Pat a) = minFreeVars c i a
  
  checkExi i (Pat p) = checkExi i p
  checkExi i e@(Abs ty v) = checkExi i ty && deepAppendError ("IN: λ : "++show ty) (checkExi (i+1) v)
  
instance CheckExi Form where  
  checkExi i (a :&: b) = checkExi i a && checkExi i b 
  checkExi i (a :@: b) = checkExi i a && checkExi i b 
  checkExi i (Bind ty v) = checkExi i ty && deepAppendError ("IN: ∀: "++show ty) (checkExi (i+1) v)
  checkExi i (viewEquiv -> (f,a,b)) = checkExi i a && checkExi i b

  minFreeVars = error "NOT A DEFINED OPERATION"
  

checkExiTop  :: (Show a , CheckExi a) => Int -> a -> Bool
checkExiTop i f = deepAppendError ("ON: "++show f) $ 
                      checkExi i f
checkExiForm :: (Show a , CheckExi a) => a -> Bool
checkExiForm f = deepAppendError ("ON: "++show f) $ 
                      checkExi 0 f