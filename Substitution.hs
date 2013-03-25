{-# LANGUAGE
 FlexibleInstances,
 PatternGuards,
 BangPatterns,
 FlexibleContexts,
 TupleSections
 #-}

module Substitution where

import AST

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

import Control.Lens hiding (Choice(..))
---------------------
--- New Variables ---
---------------------

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


newNameFor :: Name -> S.Set Name -> Name
newNameFor nm fv = nm'
  where nm' = fromJust $ find free $ nm:map (\s -> show s ++ "/?") [0..]
        free k = not $ S.member k fv
        
newName :: Name -> Map Name Spine -> S.Set Name -> (Name, Map Name Spine, S.Set Name)
newName "" so fo = ("",so, S.delete "" fo)
newName nm so fo' = (nm',s',f')
  where fo = S.delete nm fo'
        s = M.delete nm so  
        -- could reduce the size of the free variable set here, but for efficiency it is not really necessary
        -- for beautification of output it is
        (s',f') = if nm == nm' then (s,fo) else (M.insert nm (var nm') s , fo)
        nm' = fromJust $ find free $ nm:map (\s -> show s ++ "/") [0..]
        fv = mappend (M.keysSet s) (freeVariables s)
        free k = not $ S.member k fv

  
freeWithout sp [] = freeVariables sp
freeWithout (Abs nm rst) (a:lst) = S.delete nm $ freeWithout rst lst
freeWithout (Spine "#imp_abs#" [Abs nm rst]) apps = case findTyconInPrefix nm apps of
  Just (v,apps) -> S.delete nm $ freeWithout rst apps
  Nothing -> S.delete nm $ freeWithout rst apps
freeWithout l apps = freeVariables l


subst :: (Show a, Subst a) => Substitution -> a -> a
subst s a = substFree s mempty a

class Subst a where
  substFree :: Substitution -> S.Set Name -> a -> a
  
class Alpha a where  
  alphaConvert :: S.Set Name -> Map Name Name -> a -> a
  rebuildFromMem :: Map Name Name -> a -> a  


rebuildSpine :: Spine -> [Spine] -> Spine
rebuildSpine s [] = s
rebuildSpine (Spine "#imp_abs#" [Abs nm rst]) apps = case findTyconInPrefix nm apps of 
  Just (v, apps) -> rebuildSpine (Abs nm rst) (v:apps)
  Nothing -> seq sp $ irs
                      -- proof irrelevance hack
                      -- we know we can prove that type "prop" is inhabited
                      -- irs - the proof doesn't matter
                      -- rs - the proof matters
                      -- irs - here, the proof might matter, but we don't know if we can prove the thing, 
                      -- so we need to try
     where nm' = newNameFor nm $ freeVariables apps
           sp = substFree (nm |-> var nm') mempty rst
           rs = rebuildSpine sp apps
           irs = Spine "#imp_abs#" [Abs nm rst]
rebuildSpine (Spine c apps) apps' = Spine c $ apps ++ apps'
rebuildSpine (Abs nm rst) (a:apps') = let sp = substFree (nm |-> a) mempty rst
                                      in seq sp $ rebuildSpine sp apps'
  
instance Subst a => Subst [a] where
  substFree s f t = substFree s f <$> t
  
instance Alpha a => Alpha [a] where  
  alphaConvert s m l = alphaConvert s m <$> l
  rebuildFromMem s l = rebuildFromMem s <$> l
  
instance (Subst a, Subst b) => Subst (a,b) where
  substFree s f ~(a,b) = (substFree s f a , substFree s f b)

instance Subst Spine where
  substFree s f sp@(Spine "#imp_forall#" [tp, Abs nm rst]) =
       imp_forall nm (substFree s f tp) $ substFree (M.delete nm s) (S.insert nm f) rst            

  substFree s f sp@(Spine "#imp_abs#" [Abs nm rst]) =
      imp_abs_curry nm $ substFree (M.delete nm s) (S.insert nm f) rst 
  substFree s f (Abs nm rst) = Abs nm' $ substFree s' f' rst
    where (nm',s',f') = newName nm s f
  substFree s f (Spine "#tycon#" [Spine c [v]]) = Spine "#tycon#" [Spine c [substFree s f v]]
  substFree s f sp@(Spine nm apps) = let apps' = substFree s f <$> apps  in
    case s ! nm of
      Just new -> case S.null $ S.intersection f (freeWithout new apps') of
        True -> rebuildSpine new apps'
        False -> error $ 
            "can not capture free variables because implicits quantifiers can not alpha convert: "++ show sp 
            ++ "\n\tfor: "++show s
            ++ "\n\tbound by: "++show f
      _ -> Spine nm apps'
      
instance Alpha Spine where
  alphaConvert s m (Spine "#imp_forall#" [ty,Abs a r]) = imp_forall a ty $ alphaConvert (S.insert a s) (M.delete a m) r
  alphaConvert s m (Spine "#imp_abs#" [Abs a r]) = imp_abs_curry a $ alphaConvert (S.insert a s) (M.delete a m) r
  alphaConvert s m (Abs nm r) = Abs nm' $ alphaConvert (S.insert nm' s) (M.insert nm nm' m) r
    where nm' = newNameFor nm s
  alphaConvert s m (Spine "#tycon#" [Spine c [v]]) = tycon c $ alphaConvert s m v          
  alphaConvert s m (Spine a l) = Spine (fromMaybe a (m ! a)) $ alphaConvert s m l
  
  rebuildFromMem s (Spine "#imp_forall#" [ty,Abs a r]) = imp_forall a (rebuildFromMem s ty) $ rebuildFromMem (M.delete a s) r
  rebuildFromMem s (Spine "#imp_abs#" [Abs a r]) = imp_abs_curry a $ rebuildFromMem (M.delete a s) r
  rebuildFromMem s (Abs nm r) = Abs (fromMaybe nm $ M.lookup nm s) $ rebuildFromMem s r
  rebuildFromMem s (Spine a l) = Spine a' $ rebuildFromMem s l
    where a' = fromMaybe a $ M.lookup a s
                                 
  
instance Subst Decl where
  substFree sub f (Predicate s nm ty cons) = Predicate s nm (substFree sub f ty) ((\(b,(nm,t)) -> (b,(nm,substFree sub f t))) <$> cons)
  substFree sub f (Query nm ty) = Query nm (substFree sub f ty)
  substFree sub f (Define s nm val ty) = Define s nm (substFree sub f val) (substFree sub f ty)

instance Subst a => Subst (Maybe a) where
  substFree sub f p = substFree sub f <$> p
  
instance Subst FlatPred where
  substFree sub f p = p & predType %~ substFree sub f
                        & predKind %~ substFree sub f
                        & predValue %~ substFree sub f

  
-------------------------
---  Constraint types ---
-------------------------

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
  regenAbsVars (Spine "#imp_forall#" [ty,Abs a r]) = imp_forall a ty <$> regenAbsVars r
  regenAbsVars (Spine "#imp_abs#" [Abs a r]) = imp_abs_curry a <$> regenAbsVars r
  regenAbsVars (Abs a r) = do
    a' <- getNewWith $ "@rega"
    r' <- regenAbsVars $ subst (a |-> var a') r
    return $ Abs a' r'
  regenAbsVars (Spine a l) = Spine a <$> regenAbsVars l
  
  regenWithMem (Spine "#imp_forall#" [ty,Abs a r]) = imp_forall a ty <<$> regenWithMem r
  regenWithMem (Spine "#imp_abs#" [Abs a r]) = imp_abs_curry a <<$> regenWithMem r
  regenWithMem (Abs a r) = do
    a' <- getNewWith $ "@regm"
    (r', s2) <- regenWithMem $ subst (a |-> var a') r
    return $ (Abs a' r', M.insert a' a $ s2)
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


getFamily v = fromMaybe (error ("values don't have families: "++show v)) $ getFamilyM v

getFamilyM (Spine "#infer#" [_, Abs _ lm]) = getFamilyM lm
getFamilyM (Spine "#ascribe#"  (_:v:l)) = getFamilyM (rebuildSpine v l)
getFamilyM (Spine "#dontcheck#"  [v]) = getFamilyM v
getFamilyM (Spine "#forall#" [_, Abs _ lm]) = getFamilyM lm
getFamilyM (Spine "#imp_forall#" [_, Abs _ lm]) = getFamilyM lm
getFamilyM (Spine "#exists#" [_, Abs _ lm]) = getFamilyM lm
getFamilyM (Spine "#open#" (_:_:c:_)) = getFamilyM c
getFamilyM (Spine "open" (_:_:c:_)) = getFamilyM c
getFamilyM (Spine "pack" [_,_,_,e]) = getFamilyM e
getFamilyM (Spine nm' _) = Just nm'
getFamilyM v = Nothing
