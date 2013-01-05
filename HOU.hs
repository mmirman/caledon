{-# LANGUAGE  
 DeriveFunctor,
 FlexibleInstances,
 PatternGuards,
 UnicodeSyntax
 #-}
module HOU where
import Choice
import Control.Monad.State (StateT, runStateT, modify, get)
import Control.Monad.RWS (RWST, runRWST, ask, withRWST)
import Control.Monad.Error (throwError)
import Control.Monad (unless, forM_, replicateM)
import Control.Monad.Trans (lift)
import qualified Data.Foldable as F
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Functor
import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.Set as S
import Debug.Trace

-----------------------------
---  abstract syntax tree ---
-----------------------------

type Name = String

data Spine = Spine Name [Type]
           | Abs Name Type Spine 
           deriving (Eq)

type Type = Spine

getNewWith s = (++s) <$> getNew

showWithParens t = if (case t of
                          Abs{} -> True
                          Spine _ lst -> not $ null lst
                      ) then "("++show t++")" else show t 

instance Show Spine where
  show (Spine "forall" [Abs nm ty t]) = "Π "++nm++" : "++showWithParens ty++" . "++show t  
  show (Spine h t) = h++concatMap (\s -> " "++showWithParens s) t
  show (Abs nm ty t) = "λ "++nm++" : "++showWithParens ty++" . "++show t

var nm = Spine nm []
atom = var "atom"
forall x tyA v = Spine ("forall") [Abs x tyA v]

---------------------
---  substitution ---
---------------------

type Substitution = M.Map Name Spine

infixr 1 |->
infixr 0 ***
m1 *** m2 = M.union m2 (subst m2 <$> m1)
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
instance (Functor f , Subst a) => Subst (f a) where
  subst foo t = subst foo <$> t
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
data Constraint = Spine :=: Spine
                | Constraint :&: Constraint
                | Bind Quant Name Type Constraint
                deriving (Eq)
                         
instance Show Constraint where
  show (a :=: b) = show a ++" ≐ "++show b
  show (a :&: b) = show a ++" ∧ "++show b
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

--------------------------------
---  constraint context list ---
--------------------------------

data Binding = Binding { elmQuant :: Quant
                       , elmName :: Name
                       , elmType :: Type
                       , elmPrev :: Maybe Name
                       , elmNext :: Maybe Name
                       } deriving (Show)
               
instance Subst Binding where
  subst sub b = b { elmType = subst sub $ elmType b }
                    
data Context = Context { ctxtHead :: Maybe Name  
                       , ctxtMap  :: Map Name Binding 
                       , ctxtTail :: Maybe Name 
                       } deriving (Show)
                                  
instance Subst Context where               
  subst sub b = b { ctxtMap = subst sub <$> ctxtMap b }

lookupWith s a ctxt = case M.lookup a ctxt of
  Just r -> r
  Nothing -> error s

emptyContext = Context Nothing mempty Nothing

-- assumes the element is not already in the context, or it is and the only thing that is changing is it's type.
addToContext :: Context -> Binding -> Context
addToContext (Context Nothing ctxt Nothing) elm@(Binding _ nm _ Nothing Nothing) | M.null ctxt = Context (Just nm) (M.singleton nm elm) (Just nm)
addToContext c (Binding _ _ _ Nothing Nothing) = error $ "context not empty so can't add to tail: "++show c
addToContext (Context h ctxt t) elm@(Binding _ nm _ t'@(Just p) Nothing) | t' == t = Context h (M.insert p t'val $ M.insert nm elm $ ctxt) (Just nm)
  where t'val = (lookupWith "looking up p ctxt" p ctxt) { elmNext = Just nm }
addToContext _ (Binding _ _ _ _ Nothing) = error "can't add this to tail"
addToContext (Context h ctxt t) elm@(Binding _ nm _ Nothing h'@(Just n)) | h' == h = Context (Just nm) (M.insert n h'val $ M.insert nm elm $ ctxt) t
  where h'val = (lookupWith "looking up n ctxt" n ctxt) { elmPrev = Just nm }
addToContext _ (Binding _ _ _ Nothing _) = error "can't add this to head"
addToContext ctxt@Context{ctxtMap = cmap} elm@(Binding _ nm _ (Just p) (Just n)) = 
  ctxt { ctxtMap = M.insert n n'val $ M.insert p p'val $ M.insert nm elm $ cmap }
  where n'val = (lookupWith "looking up n cmap" n cmap) { elmPrev = Just nm }
        p'val = (lookupWith "looking up p cmap" p cmap) { elmNext = Just nm }


removeFromContext :: Name -> Context -> Context
removeFromContext nm ctxt@(Context h cmap t) = case M.lookup nm cmap of
  Nothing -> ctxt
  Just Binding{ elmPrev = Nothing, elmNext = Nothing } -> emptyContext
  Just Binding{ elmPrev = Nothing, elmNext = Just n } | Just nm == h -> Context (Just n) (M.insert n h' $ M.delete nm cmap) t
    where h' = (lookupWith "attempting to find new head" n cmap) { elmPrev = Nothing }
  Just Binding{ elmPrev = Just p, elmNext = Nothing } | Just nm == t -> Context h (M.insert p t' $ M.delete nm cmap) (Just p)
    where t' = (lookupWith "attempting to find new tail" p cmap) { elmNext = Nothing }
  Just Binding{elmPrev = Just cp, elmNext = Just cn } -> case () of
    _ | h == t -> Context Nothing mempty Nothing
    _ | h == Just nm -> Context (Just cn) (n' $ M.delete nm cmap) t
    _ | t == Just nm -> Context h   (p' $ M.delete nm cmap) (Just cp)
    _ -> Context h   (n' $ p' $ M.delete nm cmap) t
    where n' = M.insert cn $ (lookupWith "looking up a cmap for n'" cn cmap) { elmNext = Just cp }
          p' = M.insert cp $ (lookupWith "looking up a cmap for p'" cp cmap ) { elmPrev = Just cn }
          
addToHead quant nm tp ctxt = addToContext ctxt $ Binding quant nm tp Nothing (ctxtHead ctxt)
addToTail quant nm tp ctxt = addToContext ctxt $ Binding quant nm tp (ctxtTail ctxt) Nothing

removeHead ctxt = case ctxtHead ctxt of 
  Nothing -> ctxt
  Just a -> removeFromContext a ctxt

removeTail ctxt = case ctxtTail ctxt of 
  Nothing -> ctxt
  Just a -> removeFromContext a ctxt


-----------------------------------------------
---  the higher order unification algorithm ---
-----------------------------------------------

type Unification = StateT Context Env Substitution

getElm x = do 
  ty <- lookupConstant x
  case ty of 
    Nothing -> Left <$> (lookupWith ("looking up x c: "++show x) x ) <$> ctxtMap <$> get
    Just a -> return $ Right a

getBindings bind = do
  ctxt <- ctxtMap <$> get
  
  let gb (Binding _ nm ty p _) = (nm,ty):case p of
        Nothing -> []
        Just p -> gb $ ctxt M.! p
  return $ tail $ gb bind
  
getTypes (Spine "forall" [Abs _ ty l]) = ty:getTypes l
getTypes _ = []

unify :: Constraint -> Unification
unify cons = case cons of 
  c1 :&: c2 -> do  -- this assumes and-forall, forall-and is a rule
    sub <- unify c1
    modify $ subst sub
    (sub ***) <$> unify (subst sub c2)
  Bind quant nm ty c -> do -- this assumes and-forall, forall-and is a rule
    modify $ addToTail quant nm ty
    unify c
  Abs nm ty s :=: Abs nm' ty' s' -> do
    unify $ ty :=: ty' :&: (Bind Forall nm ty $ s :=: subst (nm' |-> var nm) s')
  Abs nm ty s :=: s' -> do
    unify $ Bind Forall nm ty $ s :=: rebuildSpine s' [var nm]
  s :=: s' | s == s' -> return mempty
  s@(Spine x yl) :=: s' -> do
    bind <- getElm x
    let constCase = case s' of -- uvar-blah?
          Spine x' _ | x /= x' -> do
            bind' <- getElm x'
            case bind' of
              Left Binding{ elmQuant = Exists } -> unify $ s' :=: s
              _ -> throwError $ "two different universal equalities: "++show cons++" WITH BIND: "++show bind'
          Spine x' yl' | x == x' -> do -- const-const
            unless (length yl == length yl') $ throwError "bad boys"        
            foldr1 (***) <$> (mapM unify $ zipWith (:=:) yl yl')
          _ -> throwError $ "uvar against a pi WITH CONS "++show cons
    case bind of 
      Right _ -> constCase
      Left Binding{ elmQuant = Forall } -> constCase
      Left bind@Binding{ elmQuant = Exists } -> do
        -- first we need to raise.
        hl <- getBindings bind
        let makeFromList eb hl = foldr (\(nm,ty) a -> forall nm ty a) eb hl
            
            makeFromType (Spine "forall" [Abs x ty z]) f = Abs x ty $ makeFromType z f
            makeFromType _ f = f            
            
            newx_args = (map (var . fst) hl)
            sub = x |-> Spine x newx_args
            ty' = makeFromList (elmType bind) hl
            yl' = map (var . fst) hl++yl
            
            addSub sub' = case M.lookup x sub' of
              Nothing -> (sub *** sub')
              Just xv -> M.insert x (rebuildSpine xv newx_args) sub'
              
        modify $ {- addToHead Exists x ty' . -} removeFromContext x
        modify $ subst sub
        -- now we can match against the right hand side
        addSub <$> case s' of -- gvar-blah?
          Spine x' y'l -> do
            bind' <- getElm x'
            case bind' of
              Right bty -> do -- gvar-const
                gvar_const (Spine x yl', ty') (Spine x' y'l, bty)
              Left Binding{ elmQuant = Exists } -> -- gvar-uvar-inside
                error "gvar-uvar-inside"
              Left Binding{ elmQuant = Forall } -> 
                if x == x' 
                then do -- gvar-gvar-same
                  error "gvar-gvar-same"
                else do -- gvar-gvar-diff
                  error "gvar-gvar-diff"
          _ -> return $  x |-> makeFromType ty' s' -- gvar-abs?
          
gvar_const (Spine x yl, aty) (Spine x' y'l, bty) = do
  let m = length y'l
      n = length yl
                    
  xm <- replicateM m $ lift $ getNewWith "@xm"
  un <- replicateM n $ lift $ getNewWith "@un"
  let vun = var <$> un
      
      toLterm (Spine "forall" [Abs _ ty r]) (ui:unr) = Abs ui ty $ toLterm r unr
      toLterm _ [] = Spine x' $ map (\xi -> Spine xi vun) xm
      toLterm _ _ = error "what the fuck"
      
      l = toLterm aty un
                    
      untylr = reverse $ zip un $ getTypes aty
      vbuild e = foldr (\(nm,ty) a -> forall nm ty a) e untylr
                    

      substBty sub (Spine "forall" [Abs vi bi r]) (xi:xmr) = (xi,vbuild $ subst sub bi)
                                                             :substBty (M.insert vi (Spine xi vun) sub) r xmr
      substBty _ _ [] = []
      substBty _ _ _ = error $ "s is not well typed"
      sub = x |-> l          
  
  modify $ flip (foldr ($)) $ uncurry (addToHead Exists) <$> substBty mempty bty xm
  
  return sub  
          
-----------------------------
--- constraint generation ---
-----------------------------
  
checkType :: Spine -> Type -> Env Constraint
checkType sp ty = case sp of
  Abs x tyA sp -> do
    e <- getNewWith "@e"
    let cons1 = forall x tyA (Spine e [var x]) :=: ty
    cons2 <- checkType ty atom
    cons3 <- addToEnv x tyA $ checkType sp (Spine e [var x])
    return $ (∃) e (forall x tyA atom) $ cons1 :&: cons2 :&: (∀) x tyA cons3
  Spine "forall" [Abs x tyA tyB] -> do
    cons1 <- checkType tyA atom
    cons2 <- addToEnv x tyA $ checkType tyB atom
    return $ (atom :=: ty) :&: cons1 :&: (∀) x tyA cons2
  Spine head args -> cty (head, reverse args) ty
    where cty (head,[]) ty = do
            mty <- (M.lookup head) <$> ask
            case mty of
              Nothing  -> throwError $ "variable: "++show head++" not found in the environment."
              Just ty' -> do
                return $ ty' :=: ty
          cty (head,arg:rest) tyB = do
            x <- getNew
            tyB' <- getNewWith "@tyB'"
            tyA <- getNewWith "@tyA"
            addToEnv tyA atom $ do
              let cons1 = Spine tyB' [arg] :=: tyB
              cons2 <- cty (head,rest) $ forall x (var tyA) $ Spine tyB' [var x]
              cons3 <- checkType arg (var tyA)
              return $ (∃) tyA atom $ (∃) tyB' (forall x (var tyA) atom) 
                $ cons1 :&: cons2 :&: cons3

------------------------------------
--- type checking initialization ---
------------------------------------
genPutStrLn s = trace s $ return ()

checkAll :: [(Name, Type)] -> Either String ()
checkAll defined = runError $ (\(a,_,_) -> a) <$> runRWST run (M.fromList consts) 0
  where consts = ("atom", atom)
               : ("forall", forall "_" (forall "" atom atom) atom)
               : defined 
        run = forM_ defined $ \(name,axiom) -> do
          constraint <- checkType axiom atom
          () <- genPutStrLn $ name ++" \n\t"++show constraint
          substitution <- runStateT (unify constraint) emptyContext
          return ()
          
test = [ ("example", forall "atx2" atom $ forall "sec" (var "atx2") atom) 
       , ("eximp", forall "atx" atom $ forall "a" (var "atx") $ Spine "example" [var "atx", var "a"])
       ]

runTest = case checkAll test of
    Left a -> putStrLn a
    Right () -> putStrLn "success"
  
