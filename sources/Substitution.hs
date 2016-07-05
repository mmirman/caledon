{-# LANGUAGE
 FlexibleInstances,
 PatternGuards,
 BangPatterns,
 FlexibleContexts,
 TupleSections
 #-}

module Substitution where

import AST
import Names
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
newNameFor "" fv = newNameFor "x" fv
newNameFor nm fv = nm'
  where nm' = fromJust $ find free $ nm:map (\s -> nm++show s) [0..]
        free k = not $ S.member k fv
        
newName :: Name -> Map Name Spine -> S.Set Name -> (Name, Map Name Spine, S.Set Name)
newName "" so fo = newName "x" so fo -- ("",so, S.delete "" fo)
newName nm so fo' = (nm',s',f')
  where fo = S.delete nm fo'
        s = M.delete nm so  
        -- could reduce the size of the free variable set here, but for efficiency it is not really necessary
        -- for beautification of output it is
        (s',f') = if nm == nm' then (s,fo) else (M.insert nm (var nm') s , fo)
        nm' = fromJust $ find free $ nm:map (\s -> nm++show s ) [0..]
        fv = mappend (M.keysSet s) (freeVariables s)
        free k = not $ S.member k fv

  
freeWithout sp [] = freeVariables sp
freeWithout (Abs nm tp rst) (a:lst) = S.delete nm $ freeWithout rst lst
freeWithout (Spine "#imp_abs#" [_, Abs nm tp rst]) apps = case findTyconInPrefix nm apps of
  Just (v,apps) -> S.delete nm $ freeWithout rst apps
  Nothing -> S.delete nm $ freeWithout rst apps
freeWithout l apps = freeVariables l


subst :: (Show a, Subst a) => Substitution -> a -> a
subst s a = substFree s mempty a
  

class Subst a where
  substFree :: Substitution -> S.Set Name -> a -> a
  etaReduce :: a -> a  
  
class Alpha a where
  alphaConvert :: S.Set Name -> Map Name Name -> a -> a
  rebuildFromMem :: Map Name Name -> a -> a  


rebuildSpine :: Spine -> [Spine] -> Spine
rebuildSpine s [] = s
rebuildSpine (Spine "#imp_abs#" [_, Abs nm ty rst]) apps = case findTyconInPrefix nm apps of 
  Just (v, apps) -> rebuildSpine (Abs nm ty rst) (v:apps)
  Nothing -> seq sp $ if ty == tipe && S.notMember nm (freeVariables rs) then rs else irs 
                      -- proof irrelevance hack
                      -- we know we can prove that type "prop" is inhabited
                      -- irs - the proof doesn't matter
                      -- rs - the proof matters
                      -- irs - here, the proof might matter, but we don't know if we can prove the thing, 
                      -- so we need to try
     where nm' = newNameFor nm $ freeVariables apps
           sp  = subst (nm |-> var nm') rst
           rs  = rebuildSpine sp apps
           irs = infer nm ty rs
rebuildSpine (Spine c apps) apps' = Spine c $ apps ++ apps'
rebuildSpine (Abs nm _ rst) (a:apps') = let sp = subst (nm |-> a) rst
                                        in seq sp $ rebuildSpine sp apps'
                                           
instance Subst a => Subst [a] where
  substFree s f t = substFree s f <$> t
  etaReduce = (etaReduce <$>)

instance Alpha a => Alpha [a] where  
  alphaConvert s m l = alphaConvert s m <$> l
  rebuildFromMem s l = rebuildFromMem s <$> l
  
instance (Subst a, Subst b) => Subst (a,b) where
  substFree s f ~(a,b) = (substFree s f a , substFree s f b)
  etaReduce ~(a,b) = (etaReduce a , etaReduce b)
  
instance Subst Spine where
  substFree s f sp@(Spine "#imp_forall#" [_, Abs nm tp rst]) =
       imp_forall nm (substFree s f tp) $ substFree (M.delete nm s) (S.insert nm f) rst            

  substFree s f sp@(Spine "#imp_abs#" [_, Abs nm tp rst]) =
      imp_abs nm (substFree s f tp) $ substFree (M.delete nm s) (S.insert nm f) rst 
      
  substFree s f (Abs nm tp rst) = Abs nm' (substFree s f tp) $ substFree s' f' rst
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
      

  etaReduce (Abs nm ty i) = case etaReduce i of
    -- TODO: this could be WAY optimized
    i@(Spine h l') -> let l = etaReduce l' in case reverse l of
      last:r | last == var nm && not (S.member nm $ freeVariables $ Spine h $ reverse r) -> Spine h $ reverse r
      _ -> Abs nm ty (Spine h l)
    i -> Abs nm ty i  
  etaReduce (Spine "#forall#" [t, Abs nm _ rst]) = forall nm t' rst'
    where t' = etaReduce t
          rst' = etaReduce rst  
  etaReduce (Spine "#imp_forall#" [t, Abs nm _ rst]) = imp_forall nm t' rst'
    where t' = etaReduce t
          rst' = etaReduce rst
  etaReduce (Spine h l) = Spine h (etaReduce l)          
  

instance Alpha Spine where
  alphaConvert s m (Spine "#imp_forall#" [_,Abs a ty r]) = imp_forall a ty $ alphaConvert (S.insert a s) (M.delete a m) r
  alphaConvert s m (Spine "#imp_abs#" [_,Abs a ty r]) = imp_abs a ty $ alphaConvert (S.insert a s) (M.delete a m) r
  alphaConvert s m (Abs nm ty r) = Abs nm' (alphaConvert s m ty) $ alphaConvert (S.insert nm' s) (M.insert nm nm' m) r
    where nm' = newNameFor nm s
  alphaConvert s m (Spine "#tycon#" [Spine c [v]]) = tycon c $ alphaConvert s m v          
  alphaConvert s m (Spine a l) = Spine (fromMaybe a (m ! a)) $ alphaConvert s m l
  
  rebuildFromMem s (Spine "#imp_forall#" [_,Abs a ty r]) = imp_forall a (rebuildFromMem s ty) $ rebuildFromMem (M.delete a s) r
  rebuildFromMem s (Spine "#imp_abs#" [_,Abs a ty r]) = imp_abs a (rebuildFromMem s ty) $ rebuildFromMem (M.delete a s) r
  rebuildFromMem s (Abs nm ty r) = Abs (fromMaybe nm $ M.lookup nm s) (rebuildFromMem s ty) $ rebuildFromMem s r
  rebuildFromMem s (Spine a l) = Spine a' $ rebuildFromMem s l
    where a' = fromMaybe a $ M.lookup a s
                                 
  
instance Subst Decl where
  substFree sub f (Predicate s nm ty cons) = Predicate s nm (substFree sub f ty) ((\(b,(nm,t)) -> (b,(nm,substFree sub f t))) <$> cons)
  substFree sub f (Query nm ty) = Query nm (substFree sub f ty)
  substFree sub f (Define s nm val ty) = Define s nm (substFree sub f val) (substFree sub f ty)

  etaReduce (Predicate s nm ty cons) = Predicate s nm (etaReduce ty) ((\(b,(nm,t)) -> (b,(nm,etaReduce t))) <$> cons)
  etaReduce (Query nm ty) = Query nm (etaReduce ty)
  etaReduce (Define s nm val ty) = Define s nm (etaReduce val) (etaReduce ty)  
instance Subst a => Subst (Maybe a) where
  substFree sub f p = substFree sub f <$> p
  etaReduce p = etaReduce <$> p
  
instance Subst FlatPred where
  substFree sub f p = p & predType %~ substFree sub f
                        & predKind %~ substFree sub f
                        & predValue %~ substFree sub f
  etaReduce p = p & predType %~ etaReduce
                  & predKind %~ etaReduce
                  & predValue %~ etaReduce
                                        
-------------------------
---  Constraint types ---
-------------------------

instance Subst SCons where
  substFree s f c = case c of
    s1 :@: s2 -> subq s f (:@:) s1 s2
    s1 :=: s2 -> subq s f (:=:) s1 s2
 
  etaReduce c = case c of               
    s1 :@: s2 -> etaReduce s1 :@: etaReduce s2 
    s1 :=: s2 -> etaReduce s1 :=: etaReduce s2 
instance Subst Constraint where
  substFree s f c = case c of
    SCons l -> SCons $ map (substFree s f) l
    s1 :&: s2 -> subq s f (:&:) s1 s2
    Bind q nm t c -> Bind q nm' (substFree s f t) $ substFree s' f' c
      where (nm',s',f') = newName nm s f

  etaReduce c = case c of
    SCons l -> SCons $ etaReduce l
    s1 :&: s2 -> etaReduce s1 :&: etaReduce s2 
    Bind q nm t c -> Bind q nm (etaReduce t) (etaReduce c)
    
subq s f e c1 c2 = e (substFree s f c1) (substFree s f c2)

(∃) :: Name -> Type -> Constraint -> Constraint
(∃) = Bind Exists

(∀) :: Name -> Type -> Constraint -> Constraint
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


getFamily v = fromMaybe (error ("values don't have families: "++show v)) $ getFamilyM v

getFamilyM (Spine "#infer#" [_, Abs _ _ lm]) = getFamilyM lm
getFamilyM (Spine "#ascribe#"  (_:v:l)) = getFamilyM (rebuildSpine v l)
getFamilyM (Spine "#dontcheck#"  [v]) = getFamilyM v
getFamilyM (Spine "#forall#" [_, Abs _ _ lm]) = getFamilyM lm
getFamilyM (Spine "#imp_forall#" [_, Abs _ _ lm]) = getFamilyM lm
getFamilyM (Spine "exists" [_, Abs _ _ lm]) = getFamilyM lm
getFamilyM (Spine "open" l) | [_,_,c] <- removeTyconPrefix l = getFamilyM c
getFamilyM (Spine "pack" l) | (c: _)  <- removeTyconPrefix l = getFamilyM c
getFamilyM (Spine nm' _) = Just nm'
getFamilyM v = Nothing

removeTyconPrefix (Spine "#tycon#" _:l) = removeTyconPrefix l
removeTyconPrefix l = l


eta_expand :: Spine -> Name -> Spine
eta_expand (Spine "#imp_forall#" [_, Abs a t1 t2]) n | n /= a = imp_abs a t1 $ Spine n [tycon a $ eta_expand t1 a]
eta_expand (Spine "#forall#" [_, Abs a t1 t2]) n = Abs a' t1 $ Spine n [eta_expand t1 a']
  where a' = newNameFor a $ S.singleton n
eta_expand _ n = var n


eta_expandAll :: M.Map Name Type -> Spine -> Spine
eta_expandAll mp (Abs a ty l) = let ty' = eta_expandAll mp ty 
                                in Abs a ty' $ eta_expandAll (M.insert a ty' mp) l
eta_expandAll mp (Spine s l) = case mp ! s of
  Nothing -> Spine s (eta_expandAll mp <$> l)
  Just t  -> rebuildSpine (eta_expand t s) (eta_expandAll mp <$> l)
  
  
