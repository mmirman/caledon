{-# LANGUAGE  
 DeriveFunctor,
 FlexibleInstances,
 PatternGuards
 #-}
module HOU where
import Choice
import Control.Monad.State (StateT, runStateT, modify, lift, unless, get, put)
import Control.Monad.Reader (ReaderT, runReaderT, ask)
import Control.Monad.Error 
import qualified Data.Foldable as F
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Functor
import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.Set as S

type Name = String

data Spine = Spine Name [Type]
           | PI Name Type Spine 
           deriving (Eq, Show, Read)

type Type = Spine

type Substitution = M.Map Name Spine

infixr 1 |->
infixr 0 ***
m1 *** m2 = M.union m2 (subst m2 <$> m1)
(|->) = M.singleton
(!) = flip M.lookup

rebuildSpine :: Spine -> [Spine] -> Spine
rebuildSpine s [] = s
rebuildSpine (Spine c apps) apps' = Spine c (apps ++ apps')
rebuildSpine (PI nm _ rst) (a:apps') = rebuildSpine (subst (nm |-> a) $ rst) apps'

var nm = Spine nm []

newName nm s = (nm',s')
  where s' = if nm == nm' then s else M.insert nm (var nm') s 
        nm' = fromJust $ find free $ nm:map (\s -> show s ++ "/") [0..]
        fv = mappend (M.keysSet s) (freeVariables s)
        free k = not $ S.member k fv

class Subst a where
  subst :: Substitution -> a -> a
instance (Functor f , Subst a) => Subst (f a) where
  subst foo t = subst foo <$> t
instance Subst Spine where
  subst s (PI nm tp rst) = PI nm' (subst s tp) $ subst s' rst
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
    PI nm t p -> (S.delete nm $ freeVariables p) `mappend` freeVariables t
    Spine head others -> mappend (S.singleton head) $ mconcat $ freeVariables <$> others

-----------------------------------------------
---  the higher order unification algorithm ---
-----------------------------------------------


data Binding = Binding { elmQuant :: Quant
                       , elmName :: Name
                       , elmType :: Type
                       , elmPrev :: Maybe Name
                       , elmNext :: Maybe Name
                       }
               
data Context = Context { ctxtHead :: Maybe Name  
                       , ctxtMap  :: Map Name Binding 
                       , ctxtTail :: Maybe Name 
                       } 

type VarGen = StateT Integer (ReaderT (Map Name Type) Choice)


-- assumes the element is not already in the context, or it is and the only thing that is changing is it's type.
addToContext :: Context -> Binding -> Context
addToContext (Context Nothing ctxt Nothing) elm@(Binding _ nm _ Nothing Nothing) | M.null ctxt = Context (Just nm) (M.singleton nm elm) (Just nm)
addToContext _ (Binding _ _ _ Nothing Nothing) = error "context not empty so can't add to tail"
addToContext (Context h ctxt t) elm@(Binding _ nm _ t'@(Just p) Nothing) | t' == t = Context h (M.insert p t'val $ M.insert nm elm $ ctxt) t'
  where t'val = (ctxt M.! p) { elmNext = Just nm }
addToContext _ (Binding _ _ _ _ Nothing) = error "can't add this to tail"
addToContext (Context h ctxt t) elm@(Binding _ nm _ Nothing h'@(Just n)) | h' == h = Context h' (M.insert n h'val $ M.insert nm elm $ ctxt) t
  where h'val = (ctxt M.! n) { elmPrev = Just nm }
addToContext _ (Binding _ _ _ Nothing _) = error "can't add this to head"
addToContext ctxt@Context{ctxtMap = cmap} elm@(Binding _ nm _ (Just p) (Just n)) = 
  ctxt { ctxtMap = M.insert n n'val $ M.insert p p'val $ M.insert nm elm $ cmap }
  where n'val = (cmap M.! n) { elmPrev = Just nm }
        p'val = (cmap M.! p) { elmNext = Just nm }

removeFromContext :: Name -> Context -> Context
removeFromContext nm ctxt@(Context h cmap t) = case M.lookup nm cmap of
  Nothing -> ctxt
  Just Binding{elmNext = cn, elmPrev = cp } -> case () of
    _ | h == t -> Context Nothing mempty Nothing
    _ | h == Just nm -> Context cn (n' $ M.delete nm cmap) t
    _ | t == Just nm -> Context h   (p' $ M.delete nm cmap) cp
    _ -> Context h   (n' $ p' $ M.delete nm cmap) t
    where n' = case cn of
            Just a -> M.insert a $ (cmap M.! a) { elmNext = cp }
            Nothing -> error "shouldn't need to remove this"
          p' = case cp of
            Just a  -> M.insert a $ (cmap M.! a) { elmPrev = cn }
            Nothing -> error "shouldn't need to remove this"  
          
addToHead quant nm tp ctxt = addToContext ctxt $ Binding quant nm tp Nothing (ctxtHead ctxt)
addToTail quant nm tp ctxt = addToContext ctxt $ Binding quant nm tp (ctxtTail ctxt) Nothing

removeHead ctxt = case ctxtHead ctxt of 
  Nothing -> ctxt
  Just a -> removeFromContext a ctxt

removeTail ctxt = case ctxtTail ctxt of 
  Nothing -> ctxt
  Just a -> removeFromContext a ctxt

data Quant = Forall | Exists

-- as ineficient as it is, I'll make this the constraint representation.
data Constraint = Spine :=: Spine
                | Constraint :&: Constraint
                | Abs Quant Name Type Constraint

instance Subst Constraint where
  subst s (s1 :=: s2) = subst s s1 :=: subst s s2
  subst s (c1 :&: c2) = subst s c1 :&: subst s c2
  subst s (Abs q nm t c) = Abs q nm (subst s t) $ subst (M.delete nm s) c

type Unification = StateT Context VarGen Substitution

lookupConstant x = (M.lookup x) <$> lift ask

getElm x = do 
  ty <- lift $ lookupConstant x
  case ty of 
    Nothing -> Left <$> (M.! x) <$> ctxtMap <$> get
    Just a -> return $ Right a

getBindings bind = do
  ctxt <- ctxtMap <$> get
  
  let gb (Binding _ nm ty p _) = (nm,ty):case p of
        Nothing -> []
        Just p -> gb $ ctxt M.! p
  return $ tail $ gb bind
  
unify :: Constraint -> Unification
unify cons = case cons of 
  c1 :&: c2 -> do        -- this assumes and-forall, forall-and is a rule
    sub <- unify c1 
    (sub ***) <$> unify (subst sub c2)
  Abs quant nm ty c -> do -- this assumes and-forall, forall-and is a rule
    modify $ addToTail quant nm ty
    unify c
  PI nm ty s :=: PI nm' ty' s' -> do
    unify $ ty :=: ty' :&: (Abs Forall nm ty $ s :=: subst (nm' |-> var nm) s')
  PI nm ty s :=: s' -> do
    unify $ Abs Forall nm ty $ s :=: rebuildSpine s' [var nm]
  s :=: s' | s == s' -> return mempty
  s@(Spine x yl) :=: s' -> do
    bind <- getElm x
    let constCase = case s' of -- uvar-blah?
          Spine x' yl' | x /= x' -> do
            bind' <- getElm x
            case bind' of
              Left Binding{ elmQuant = Exists } -> unify $ s' :=: s
              _ -> throwError "two different universal equalities"
          Spine x' yl' | x == x' -> do -- const-const
            unless (length yl == length yl') $ throwError "bad boys"        
            foldr1 (***) <$> (mapM unify $ zipWith (:=:) yl yl')
          _ -> throwError "uvar against a pi"
    case bind of 
      Right _ -> constCase
      Left bind@Binding{ elmQuant = Forall } -> constCase
      Left bind@Binding{ elmQuant = Exists } -> do
        -- first we need to raise.
        hl <- getBindings bind
        let makeFromList eb hl = foldr (\(nm,ty) a -> PI nm ty a) eb hl
            
            makeFromType (Spine _ _) f = f
            makeFromType (PI x ty z) f = PI x ty $ makeFromType z f
            
            sub = x |-> Spine x (map (var . fst) hl)
            ty' = makeFromList (elmType bind) hl
            yl' = map (var . fst) hl++yl
        modify $ {- addToHead Exists x ty' . -} removeFromContext x
        
        -- now we can match against the right hand side
        (sub ***) <$> case s' of -- gvar-blah?
          PI _ _ _ -> return $ x |-> makeFromType ty' s'
          Spine x' y'l -> do
            bind' <- getElm x
            case bind' of
              Right _ -> undefined -- gvar-const
              Left Binding{ elmQuant = Exists } -> undefined -- gvar-uvar-inside
              Left Binding{ elmQuant = Forall } -> undefined -- gvar-gvar 
                 -- gvar-gvar-same
                 -- gvar-gvar-diff
        