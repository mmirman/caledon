{-# LANGUAGE ViewPatterns              #-}
module Src.Substitution where

import Src.AST
import Src.Context
import Control.Spoon

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
substP t ctxt na (p :+: n) = 
  -- only eta expand heads and not arguments!
  hered t ctxt (substP t ctxt na p) (substN False ctxt na n)

hered :: Context c => Bool -> c -> (Either P N, Type) -> N -> (Either P N, Type)
hered t ctxt (Right p1@(Abs a1 n), l) nv = 
  ( Right $ liftV (-1) $ substN t (putTy ctxt a1) (liftV 1 nv,liftV 1 a1,DeBr 0) n
  , case viewForallP l of 
    Just ~(a1',a2) -> liftV (-1) $ substTy (putTy ctxt a1') (liftV 1 nv,liftV 1 a1',DeBr 0) a2
    Nothing -> error $ show p1++" r: "++show l
  )  
hered _ ctxt (Right (Pat p1), l) nv = 
  ( Right $ Pat $ p1 :+: nv
  , case viewForallP l of
     Just ~(a1',a2) -> liftV (-1) $ substTy (putTy ctxt a1') (liftV 1 nv, liftV 1 a1',DeBr 0) a2
     Nothing -> error $ show p1++" r: "++show l
  )
hered _ ctxt (Left p1, l) nv = 
  ( Left $ p1 :+: nv
  , case viewForallP l of
    Just ~(a1',a2) -> liftV (-1) $ substTy (putTy ctxt a1') (liftV 1 nv, liftV 1 a1',DeBr 0) a2
    Nothing -> error $ show p1++" l: "++show l
  )

substTy c s t = case substP False c s t of
  ((Left a),_) -> a -- might want to make this lazier
  ((Right (Pat a)),_) -> a -- might want to make this lazier
  ((Right (Abs{})),_) -> error "not a type"

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

subst c s f = substF c s f {- case spoon (substF c s f) of
  Nothing -> error $ "SUBST: ["++show s++" ] " ++ show f ++ "\nCTXT: "++show c
  Just a  -> a -}

app  :: Context c => c -> Either P N -> N -> Either P N
app ctxt (Right (Abs a1 n)) nv = Right $ liftV (-1) $ substN True (putTy ctxt a1) (liftV 1 nv,liftV 1 a1,DeBr 0) n
app _ (Right (Pat p1)) nv = Right $ Pat (p1 :+: nv)
app _ (Left p1) nv = Left $ p1 :+: nv

app'  :: Either P N -> N -> Either P N
app' (Right (Abs a1 n)) nv = Right $ liftV (-1) $ substN False (error "just a substitution, no eta" :: ()) (liftV 1 nv,liftV 1 a1,DeBr 0) n
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

freeVarsP (Var (Exi _ nm t)) = S.insert nm $ freeVarsP t
freeVarsP (Var _) = mempty
freeVarsP (p :+: n) = freeVarsP p `mappend` freeVarsN n

freeVarsMapN (Pat p) = freeVarsMapP p
freeVarsMapN (Abs t1 t2) = freeVarsMapP t1 `mappend` freeVarsMapN t2

freeVarsMapP (Var (Exi _ nm t)) = M.insert nm t $ freeVarsMapP t
freeVarsMapP (Var _) = mempty
freeVarsMapP (p :+: n) = freeVarsMapP p `mappend` freeVarsMapN n
