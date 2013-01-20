{-# LANGUAGE  
 DeriveFunctor,
 FlexibleInstances,
 PatternGuards,
 UnicodeSyntax
 #-}
module HOU where
import Choice
import Control.Monad.State (StateT, runStateT, modify, get, put)
import Control.Monad.RWS (RWST, runRWST, ask, withRWST)
import Control.Monad.Error (throwError)
import Control.Monad (unless, forM_, replicateM)
import Control.Monad.Trans (lift)
import Control.Applicative
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
type Term = Spine

getNewWith s = (++s) <$> getNew

showWithParens t = if (case t of
                          Abs{} -> True
                          Spine _ lst -> not $ null lst
                      ) then "("++show t++")" else show t 

instance Show Spine where
  show (Spine "forall" [Abs nm ty t]) = "Π "++nm++" : "++showWithParens ty++" . "++show t  
  show (Spine "exists" [Abs nm ty t]) = "Σ "++nm++" : "++showWithParens ty++" . "++show t  
  show (Spine h t) = h++concatMap (\s -> " "++showWithParens s) t
  show (Abs nm ty t) = "λ "++nm++" : "++showWithParens ty++" . "++show t

var nm = Spine nm []
atom = var "atom"
forall x tyA v = Spine ("forall") [Abs x tyA v]
exists x tyA v = Spine ("exists") [Abs x tyA v]


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
addToContext (Context Nothing ctxt Nothing) elm@(Binding _ nm _ Nothing Nothing) | M.null ctxt = checkContext "addToCtxt N N" $ 
                                                                                                 Context (Just nm) (M.singleton nm elm) (Just nm)
addToContext c (Binding _ _ _ Nothing Nothing) = error $ "context not empty so can't add to tail: "++show c
addToContext (Context h ctxt t) elm@(Binding _ nm _ t'@(Just p) Nothing) | t' == t = checkContext "addToCtxt J N" $ 
  Context h (M.insert p t'val $ M.insert nm elm $ ctxt) (Just nm)
  where t'val = (lookupWith "looking up p ctxt" p ctxt) { elmNext = Just nm }
addToContext _ (Binding _ _ _ _ Nothing) = error "can't add this to tail"
addToContext (Context h ctxt t) elm@(Binding _ nm _ Nothing h'@(Just n)) | h' == h = checkContext "addToCtxt N J" $ 
  Context (Just nm) (M.insert n h'val $ M.insert nm elm $ ctxt) t
  where h'val = (lookupWith "looking up n ctxt" n ctxt) { elmPrev = Just nm }
addToContext _ (Binding _ _ _ Nothing _) = error "can't add this to head"
addToContext ctxt@Context{ctxtMap = cmap} elm@(Binding _ nm _ (Just p) (Just n)) = checkContext "addToCtxt J J" $ 
  ctxt { ctxtMap = M.insert n n'val $ M.insert p p'val $ M.insert nm elm $ cmap }
  where n'val = (lookupWith "looking up n cmap" n cmap) { elmPrev = Just nm }
        p'val = (lookupWith "looking up p cmap" p cmap) { elmNext = Just nm }
  
removeFromContext :: Name -> Context -> Context
removeFromContext nm ctxt@(Context h cmap t) = case M.lookup nm cmap of
  Nothing -> checkContext "removing: nothing" $ ctxt
  Just Binding{ elmPrev = Nothing, elmNext = Nothing } -> emptyContext
  Just Binding{ elmPrev = Nothing, elmNext = Just n } | Just nm == h -> checkContext "removing: N J" $ Context (Just n) (M.insert n h' $ M.delete nm cmap) t
    where h' = (lookupWith "attempting to find new head" n cmap) { elmPrev = Nothing }
  Just Binding{ elmPrev = Just p, elmNext = Nothing } | Just nm == t -> checkContext "removing: J N" $ Context h (M.insert p t' $ M.delete nm cmap) (Just p)
    where t' = (lookupWith "attempting to find new tail" p cmap) { elmNext = Nothing }
  Just Binding{elmPrev = Just cp, elmNext = Just cn } -> case () of
    _ | h == t -> checkContext "removing: J J | h == t " $ Context Nothing mempty Nothing
    _ | h == Just nm -> checkContext "removing: J J | h == Just nm  " $ Context (Just cn) (n' $ M.delete nm cmap) t
    _ | t == Just nm -> checkContext "removing: J J | t == Just nm  " $ Context h   (p' $ M.delete nm cmap) (Just cp)
    _ -> checkContext ("removing: J J | h /= t \n\t"++show ctxt) $ Context h (n' $ p' $ M.delete nm cmap) t
    where n' = M.insert cn $ (lookupWith "looking up a cmap for n'" cn cmap) { elmPrev = Just cp }
          p' = M.insert cp $ (lookupWith "looking up a cmap for p'" cp cmap ) { elmNext = Just cn }
          
addToHead quant nm tp ctxt = addToContext ctxt $ Binding quant nm tp Nothing (ctxtHead ctxt)
addToTail quant nm tp ctxt = addToContext ctxt $ Binding quant nm tp (ctxtTail ctxt) Nothing

removeHead ctxt = case ctxtHead ctxt of 
  Nothing -> ctxt
  Just a -> removeFromContext a ctxt

removeTail ctxt = case ctxtTail ctxt of 
  Nothing -> ctxt
  Just a -> removeFromContext a ctxt

getTail (Context _ ctx (Just t)) = lookupWith "getting tail" t ctx
getHead (Context (Just h) ctx _) = lookupWith "getting head" h ctx

getEnd s bind ctx@(Context{ ctxtMap = ctxt }) = tail $ gb bind
  where gb (Binding _ nm ty _ n) = (nm,ty):case n of
          Nothing -> []
          Just n -> gb $ case M.lookup n ctxt of 
            Nothing -> error $ "element "++show n++" not in map \n\twith ctxt: "++show ctx++" \n\t for bind: "++show bind++"\n\t"++s
            Just c -> c

getStart s bind ctx@(Context{ ctxtMap = ctxt }) = tail $ gb bind
  where gb (Binding _ nm ty p _) = (nm,ty):case p of
          Nothing -> []
          Just p -> gb $ case M.lookup p ctxt of 
            Nothing -> error $ "element "++show p++" not in map \n\twith ctxt: "++show ctx++" \n\t for bind: "++show bind++"\n\t"++s
            Just c -> c
            
checkContext s c@(Context Nothing _ Nothing) = c
checkContext s ctx = foldr seq ctx $ zip st ta
  where st = getStart s (getTail ctx) ctx
        ta = getEnd s (getHead ctx) ctx

-----------------------------------------------
---  the higher order unification algorithm ---
-----------------------------------------------

type WithContext = StateT Context Env 

type Unification = WithContext Substitution

getElm :: Name -> Name -> WithContext (Either Binding Spine)
getElm s x = do
  ty <- lookupConstant x
  case ty of
    Nothing -> Left <$> (\ctxt -> lookupWith ("looking up "++x++"\n\t in context: "++show ctxt++"\n\t"++s) x ctxt) <$> ctxtMap <$> get
    Just a -> return $ Right a

-- | This gets all the bindings outside of a given bind and returns them in a list.
getBindings :: Binding -> WithContext [(Name,Type)]
getBindings bind = do
  ctx <- get
  return $ getStart "IN: getBindings" bind ctx

getTypes :: Spine -> [Type]
getTypes (Spine "forall" [Abs _ ty l]) = ty:getTypes l
getTypes _ = []

flatten :: Constraint -> ([(Quant, Name, Type)], [(Spine, Spine)])
flatten cons = case cons of
  Top -> ([],[])
  c1 :&: c2 -> let (binds1,c1') = flatten c1
                   (binds2,c2') = flatten c2
               in (binds1++binds2,c1'++c2')
  Bind quant nm ty c -> ((quant,nm,ty):binds,c')
    where (binds, c') = flatten c
  a :=: b -> ([],[(a,b)])
  
addBinds :: [(Quant, Name, Type)] -> WithContext ()
addBinds binds = mapM_ (\(quant,nm,ty) -> modify $ addToTail quant nm ty) binds   

  
isolate m = do
  s <- get
  a <- m
  s' <- get
  put s
  return (s',a)
  
unify :: Constraint -> Unification
unify cons = do
  cons <- lift $ regenAbsVars cons
  let (binds,constraints) = flatten cons
  addBinds binds      
  let uniOne [] r  = throwError "can not unify any further"
      uniOne ((a,b):l) r = do
        (newstate,choice) <- isolate $ unifyEq a b
        case choice of
          Just (sub,cons) -> do
            let (binds,constraints) = flatten cons
            put newstate
            addBinds binds
            let l' = subst sub <$> l
                r' = subst sub <$> reverse r
            return $ (sub,l'++constraints++r')
          Nothing -> uniOne l ((a,b):r)
     
      uniWhile [] = return mempty
      uniWhile l = do 
        (sub,l') <- uniOne l []
        modify $ subst sub
        (sub ***) <$> uniWhile l'
      
  uniWhile constraints

unifyEq :: Spine -> Spine -> WithContext (Maybe (Substitution , Constraint))
unifyEq a b = let cons = a :=: b in case cons of 
  Abs nm ty s :=: Abs nm' ty' s' -> do
    return $ Just (mempty, ty :=: ty' :&: (Bind Forall nm ty $ s :=: subst (nm' |-> var nm) s'))
  Abs nm ty s :=: s' -> do
    return $ Just (mempty, Bind Forall nm ty $ s :=: rebuildSpine s' [var nm])
  s :=: s' | s == s' -> return $ Just (mempty, Top)
  s@(Spine x yl) :=: s' -> do
    bind <- getElm ("all: "++show cons) x
    let constCase = Just <$> case s' of
          Spine x' _ | x /= x' -> do
            bind' <- getElm ("const case: "++show cons) x'
            case bind' of
              Left Binding{ elmQuant = Exists } -> return $ (mempty,s' :=: s)
              _ -> throwError $ "two different universal equalities: "++show cons++" WITH BIND: "++show bind'
          Spine x' yl' | x == x' -> do -- const-const
            unless (length yl == length yl') $ throwError $ "different numbers of arguments on constant: "++show cons
            return (mempty, foldl (:&:) Top $ zipWith (:=:) yl yl')
          _ -> throwError $ "uvar against a pi WITH CONS "++show cons
          
    case bind of
      Right _ -> constCase
      Left Binding{ elmQuant = Forall } | S.member x $ freeVariables yl -> throwError $ "occurs check: "++show (a :=: b)
      Left Binding{ elmQuant = Forall } -> constCase
      Left bind@Binding{ elmQuant = Exists } -> do
        raiseToTop bind (Spine x yl) $ \a@(Spine x yl) ty -> 
          case s' of 
            Spine x' y'l -> do
              bind' <- getElm "gvar-blah" x'
              case bind' of
                Right ty' -> -- gvar-const
                  gvar_const (Spine x yl, ty) (Spine x' y'l, ty') 
                Left Binding{ elmQuant = Forall } | not $ S.member x' $ freeVariables yl -> throwError $ "gvar-uvar-depends: "++show (a :=: b)
                Left Binding{ elmQuant = Forall } | S.member x $ freeVariables yl -> throwError $ "occurs check: "++show (a :=: b)
                Left Binding{ elmQuant = Forall, elmType = ty' } -> -- gvar-uvar-inside
                  gvar_uvar_inside (Spine x yl, ty) (Spine x' y'l, ty')
                Left bind@Binding{ elmQuant = Exists, elmType = ty' } -> 
                  if not $ allElementsAreVariables yl && allElementsAreVariables y'l 
                  then return Nothing 
                  else if x == x' 
                       then -- gvar-gvar-same
                         gvar_gvar_same (Spine x yl, ty) (Spine x' y'l, ty')
                       else -- gvar-gvar-diff
                         if S.member x $ freeVariables y'l 
                         then throwError $ "occurs check: "++show (a :=: b)
                         else gvar_gvar_diff (Spine x yl, ty) (Spine x' y'l, ty') bind
            _ -> return $ Just (x |-> makeFromType ty s',Top) -- gvar-abs?
            
allElementsAreVariables :: [Spine] -> Bool
allElementsAreVariables = all $ \c -> case c of
  Spine a [] -> True
  _ -> False

makeFromType (Spine "forall" [Abs x ty z]) f = Abs x ty $ makeFromType z f
makeFromType _ f = f

makeFromList eb hl = foldr (\(nm,ty) a -> forall nm ty a) eb hl

typeToListOfTypes (Spine _ _) = []
typeToListOfTypes (Abs x ty l) = (x,ty):typeToListOfTypes l


raiseToTop bind@Binding{ elmName = x, elmType = ty } sp m = do
  hl <- getBindings bind
  let newx_args = (map (var . fst) hl)
      sub = x |-> Spine x newx_args
      ty' = makeFromList (elmType bind) hl
            
      addSub Nothing = Nothing
      addSub (Just (sub',cons)) = case M.lookup x sub' of
        Nothing -> Just (sub *** sub', cons)
        Just xv -> Just (M.insert x (rebuildSpine xv newx_args) sub', cons)
              
  modify $ addToHead Exists x ty' . removeFromContext x
  modify $ subst sub
  -- now we can match against the right hand side
  l <- addSub <$> m (subst sub sp) ty'
  modify $ removeFromContext x
  return l

-- TODO: make sure this is correct.  its now just a modification of gvar_gvar_diff!
gvar_gvar_same (Spine x yl, aty) (Spine x' y'l, bty) = do
  let n = length yl
      m = length y'l
                    
      (uNl,atyl) = unzip $ take n $ typeToListOfTypes aty
      (vNl,btyl) = unzip $ take m $ typeToListOfTypes bty
      
  xN <- lift $ getNewWith "@x'"
  
  let perm = [iyt | (iyt,_) <- filter (\(_,(a,b)) -> a == b) $ zip (zip uNl atyl) (zip yl y'l) ]
      
      makeBind us tyl arg = foldr (uncurry Abs) (Spine xN $ map var arg) $ zip us tyl
      
      l = makeBind uNl atyl $ map fst perm
      
      getBase 0 a = a
      getBase n (Spine "forall" [Abs _ ty r]) = getBase (n - 1) r
      getBase _ a = a
      
      xNty = foldr (uncurry forall) (getBase n aty) perm
      
      sub = x |-> l
      
  modify $ addToHead Exists xN xNty
  return $ Just (sub, Top)

  
gvar_gvar_diff (Spine x yl, aty) (sp, _) bind = raiseToTop bind sp $ \(Spine x' y'l) bty -> do
  
  -- now x' comes before x 
  -- but we no longer care since I tested it, and switching them twice reduces to original
  let n = length yl
      m = length y'l
                    
      (uNl,atyl) = unzip $ take n $ typeToListOfTypes aty
      (vNl,btyl) = unzip $ take m $ typeToListOfTypes bty
      
  xN <- lift $ getNewWith "@x'"
  
  let perm = [(iyt,i') | (iyt,y) <- zip (zip uNl atyl) yl, (i',_) <- filter (\(_,y') -> y == y') $ zip vNl y'l ]
      
      makeBind us tyl arg = foldr (uncurry Abs) (Spine xN $ map var arg) $ zip us tyl
      
      l = makeBind uNl atyl $ map (fst . fst) perm
      l' = makeBind vNl btyl $ map snd perm
      
      getBase 0 a = a
      getBase n (Spine "forall" [Abs _ ty r]) = getBase (n - 1) r
      getBase _ a = a
      
      xNty = foldr (uncurry forall) (getBase n aty) (map fst perm)
      
      sub = (x |-> l) *** (x' |-> l')
      
  modify $ addToHead Exists xN xNty
  return $ Just (sub, Top)
  
  
gvar_uvar_inside a@(Spine _ yl, _) b@(Spine y _, _) = 
  case elemIndex (var y) yl of
    Nothing -> return Nothing
    Just i -> gvar_fixed a b (!! i)

gvar_const a b@(Spine x' _, _) = gvar_fixed a b (const x')


gvar_fixed (a@(Spine x yl), aty) (b@(Spine x' y'l), bty) action = do
  let m = length y'l
      n = length yl
                    
  xm <- replicateM m $ lift $ getNewWith "@xm"
  un <- replicateM n $ lift $ getNewWith "@un"
  let vun = var <$> un
      

      toLterm (Spine "forall" [Abs _ ty r]) (ui:unr) = Abs ui ty <$> toLterm r unr
      toLterm _ [] = return $ Spine (action un) $ map (\xi -> Spine xi vun) xm

      toLterm s l = throwError $ "too many arguments for this type: "
                    ++"\n\ts: "++show s
                    ++"\n\taty: "++show aty
                    ++"\n\tinitials: "++show l
                    ++"\n\tcons: "++show (a :=: b)
  l <- toLterm aty un
  
  let untylr = reverse $ zip un $ getTypes aty
      vbuild e = foldr (\(nm,ty) a -> forall nm ty a) e untylr
                    

      substBty sub (Spine "forall" [Abs vi bi r]) (xi:xmr) = (xi,vbuild $ subst sub bi)
                                                             :substBty (M.insert vi (Spine xi vun) sub) r xmr
      substBty _ _ [] = []
      substBty _ _ _ = error $ "s is not well typed"
      sub = x |-> l          
  
  modify $ flip (foldr ($)) $ uncurry (addToHead Exists) <$> substBty mempty bty xm
  
  return $ Just (sub, Top)

--------------------
--- proof search ---  
--------------------
getEnv :: WithContext Constants
getEnv = do  
  nmMapA <- lift $ ask  
  nmMapB <- (fmap elmType . ctxtMap) <$> get
  return $ M.union nmMapB nmMapA 
  
search :: Type -> WithContext (Substitution, Term)
search goal = case goal of 
  Spine "exists" [Abs nm ty lm] -> do
    
    -- this case is a bit strange as we rely on unification, either now
    -- OR in the FUTURE in order to find the actual value for tau/nm'
    -- so we can't delete nm' from the context.
    
    nm' <- lift $ getNewWith "@search"
    modify $ addToTail Exists nm' ty
    
    (sub, e) <- search $ subst (nm |-> var nm') lm 
    return $ (sub, Spine "#pack#" [e, subst sub $ var nm', Abs nm ty lm])
    
  Spine "forall" [Abs nm ty lm] -> do
    nm' <- lift $ getNewWith "@sr"
    modify $ addToTail Forall nm' ty
    (sub,l) <- search $ subst (nm |-> var nm') lm
    modify $ removeFromContext nm'
    return (sub, Abs nm' (subst sub ty) l)
  Spine nm args -> fail "" <|> do -- here we ensure that since this might run infinitely deep without different cases, we stop somewhere along the way 
                                  -- to give other branches a fair shot at computation.
    env <- M.toList <$> getEnv
    
    let sameFamily (Spine nm' args) | nm == nm' =  True
        sameFamily (Spine "forall" [Abs _ _ lm]) = sameFamily lm
        sameFamily (Spine "exists" [Abs _ _ lm]) = sameFamily lm
        sameFamily _ = False

        left x target = case target of 
          Spine "forall" [Abs nm ty lm] -> do
            nm' <- lift $ getNewWith "@sla"
            -- by using existential quantification we can defer search implicitly
            modify $ addToTail Exists nm' ty
            (sub, result)  <- left x $ subst (nm |-> var nm') lm
            return $ (sub, \l -> result $ (subst sub $ var nm'):l )
            
          Spine "exists" [Abs nm ty lm] -> do 
            nm' <- lift $ getNewWith "@sle"
            -- universal quantification as information hiding
            modify $ addToTail Forall nm' ty
            (sub,result) <- left x $ subst (nm |-> var nm') lm
            modify $ removeFromContext nm'
            
            p <- lift $ getNewWith "@p"
            return (sub, \l -> Spine "#open#" 
                               [result [], Abs nm' ty $ Abs p (subst (nm |-> var nm') lm) $ Spine p l])

          Spine _ _ -> do  
            sub <- unify $ goal :=: target
            return (sub, \l -> Spine x l)
          _ -> error $ "λ does not have type atom: " ++ show target
        
        leftInit (x,target) = do
          (sub,l) <- left x target
          return (sub, subst sub $ l [])
          
    F.msum $ leftInit <$> filter (sameFamily . snd) env

  _ -> error $ "Not a type: "++show goal
  
  
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

  Spine "#spack#" [e, tau] -> do
    tp <- getNewWith "@tp"
    imp <- getNewWith "@imp"
    iface <- getNewWith "@iface"
    
    let vtp = var tp
        ifaceTp = forall "_" vtp atom
        
    cons1 <- addToEnv tp atom $ checkType tau vtp
    
    cons2 <- addToEnv tp atom
             $ addToEnv iface ifaceTp
             $ checkType e $ Spine iface [tau]
    
    return $ (∃) tp atom $ cons1
         :&: ((∃) iface ifaceTp $ cons2 :&: ty :=: exists imp vtp (Spine iface [var imp]))
      
  Spine "#pack#" [e, tau, Abs imp tp interface] -> do
    cons1 <- checkType tp atom    
    cons2 <- checkType tau tp
    cons3 <- checkType e (subst (imp |-> tau) interface)
    return $ cons1 
         :&: cons2 
         :&: cons3
         :&: ty :=: exists imp tp interface
    
  Spine "#sopen#" (closed:l) -> do
    tp <- getNewWith "@tp"
    imp <- getNewWith "@imp"
    iface <- getNewWith "@iface"
    p <- getNewWith "@p"
    
    let vimp = var imp
        vtp = var tp
        ifaceTp = forall "_" vtp atom
        ifaceImp = Spine iface [vimp]

    cons <- addToEnv tp atom $ addToEnv iface ifaceTp $ do
      
      cons1 <- checkType closed $ exists imp vtp $ ifaceImp
      
      cons2 <- addToEnv imp vtp $ addToEnv p ifaceImp $ checkType (Spine p l) ty
        
      return $ cons1 :&: ((∃) imp vtp $ (∀) p ifaceImp cons2 )

    return $ (∃) tp atom $ (∃) iface ifaceTp $ cons 
  
  Spine "#open#" [closed, Abs imp tp (Abs p interface exp)] -> do
    cons1 <- checkType tp atom
    cons2 <- checkType closed $ exists imp tp interface
    cons3 <- addToEnv imp tp $ do
      cons1 <- checkType interface atom
      cons2 <- addToEnv p interface $ checkType exp ty    
      return $ cons1 :&: (∀) p interface cons2
      
    return $ cons1 :&: cons2 :&: (∃) imp tp cons3 
    
  Spine "forall" [Abs x tyA tyB] -> do
    cons1 <- checkType tyA atom
    cons2 <- addToEnv x tyA $ checkType tyB atom
    return $ atom :=: ty :&: cons1 :&: (∀) x tyA cons2
  Spine "exists" [Abs x tyA tyB] -> do
    cons1 <- checkType tyA atom
    cons2 <- addToEnv x tyA $ checkType tyB atom
    return $ atom :=: ty :&: cons1 :&: (∃) x tyA cons2    
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

infixr 0 ~>
(~>) = forall ""

-- [(Name, [(Name,Type)] , Type)]
-- convert this into something that typechecks it as "exists e : t . t'" then substitutes for 
-- e, when the jig is up.
checkAll :: [(Name, Type)] -> Either String ()
checkAll defined = runError $ (\(a,_,_) -> a) <$> runRWST run (M.fromList consts) 0
  where consts = ("atom", atom)
               : ("forall", (atom ~> atom) ~> atom)
               : ("exists", (atom ~> atom) ~> atom)
               : ("#pack#", exists "tp" atom $ exists "a" atom $  var "a" ~> var "tp" ~> forall "imp" (var "tp" ~> atom) $ exists "i" atom $ Spine "imp" [var "i"])
               : ("#spack#", exists "tp" atom $ exists "a" atom $ exists "imp" (var "tp" ~> atom) $ var "a" ~> var "tp" ~> exists "i" atom $ Spine "imp" [var "i"])
               : defined 
        run = forM_ defined $ \(name,axiom) -> do
          constraint <- checkType axiom atom
          () <- genPutStrLn $ name ++" \n\t"++show constraint
          substitution <- runStateT (unify constraint) emptyContext
          return ()
          
test = [ ("example", exists "z2" atom $ forall "atx2" (var "z2") $ forall "sec" (var "atx2") atom) 
       , ("eximp1", forall "atx" atom $ forall "a" (var "atx") $ 
                    Spine "#open#" [ Spine "example" []
                                   , Abs "z3" atom $ Abs "examp" (forall "atx2" (var "z3") $ forall "sec" (var "atx2") atom)
                                   $ Spine "examp" [var "atx", var "a"] 
                                   ])
       , ("eximp2", forall "atx" atom $ forall "a" (var "atx") $ 
                    exists "tp" (forall "_" atom atom) $ 
                    Spine "#open#" [ Spine "example" []
                                   , Abs "z3" atom $ Abs "examp" (Spine "tp" [var "z3"])
                                   $ Spine "examp" [var "atx", var "a"] 
                                   ])
       , ("eximp3", forall "atx" atom $ forall "a" (var "atx") $ 
                    Spine "#sopen#" [ Spine "example" []
                                    , var "atx"
                                    , var "a"
                                    ])
       ]

runTest = case checkAll test of
    Left a -> putStrLn a
    Right () -> putStrLn "success"
  
