module Context where

import AST
import Data.Monoid
import Data.Functor
import qualified Data.Map as M
import Data.Map (Map)
import Control.Monad.State (StateT, runStateT, modify, get, put)
import Data.List
import Debug.Trace

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
  Just Binding{ elmPrev = Nothing, elmNext = Just n } -> isSane (Just nm == h) $ checkContext "removing: N J" $ Context (Just n) (M.insert n h' $ M.delete nm cmap) t
    where h' = (lookupWith "attempting to find new head" n cmap) { elmPrev = Nothing }
  Just Binding{ elmPrev = Just p, elmNext = Nothing } -> isSane (Just nm == t) $ checkContext "removing: J N" $ Context h (M.insert p t' $ M.delete nm cmap) (Just p)
    where t' = (lookupWith "attempting to find new tail" p cmap) { elmNext = Nothing }
  Just Binding{elmPrev = Just cp, elmNext = Just cn } -> case () of
    _ | h == t -> checkContext "removing: J J | h == t " $ Context Nothing mempty Nothing
    _ | h == Just nm -> checkContext "removing: J J | h == Just nm  " $ Context (Just cn) (n' $ M.delete nm cmap) t
    _ | t == Just nm -> checkContext "removing: J J | t == Just nm  " $ Context h   (p' $ M.delete nm cmap) (Just cp)
    _ -> checkContext ("removing: J J | h /= t \n\t"++show ctxt) $ Context h (n' $ p' $ M.delete nm cmap) t
    where n' = M.insert cn $ (lookupWith "looking up a cmap for n'" cn cmap) { elmPrev = Just cp }
          p' = M.insert cp $ (lookupWith "looking up a cmap for p'" cp cmap ) { elmNext = Just cn }
  where isSane bool a = if bool then a else error "This doesn't match intended binding"

addToHead quant nm tp ctxt = addToContext ctxt $ Binding quant nm tp Nothing (ctxtHead ctxt)
addToTail quant nm tp ctxt = addToContext ctxt $ Binding quant nm tp (ctxtTail ctxt) Nothing

removeHead ctxt = case ctxtHead ctxt of 
  Nothing -> ctxt
  Just a -> removeFromContext a ctxt

removeTail ctxt = case ctxtTail ctxt of 
  Nothing -> ctxt
  Just a -> removeFromContext a ctxt

getTail (Context _ ctx (Just t)) = lookupWith "getting tail" t ctx
getTail (Context _ _ Nothing) = error "no tail!"

getHead (Context (Just h) ctx _) = lookupWith "getting head" h ctx
getHead (Context Nothing _ _) = error "no head"

-- gets the list of bindings after (below) a given binding
getAfter s bind ctx@(Context{ ctxtMap = ctxt }) = tail $ gb bind
  where gb ~(Binding quant nm ty _ n) = (quant, (nm,ty)):case n of
          Nothing -> []
          Just n -> gb $ case M.lookup n ctxt of 
            Nothing -> error $ "element "++show n++" not in map \n\twith ctxt: "++show ctx++" \n\t for bind: "++show bind++"\n\t"++s
            Just c -> c

-- gets the list of bindings before (above) a given binding
getBefore s bind ctx@(Context{ ctxtMap = ctxt }) = tail $ gb bind
  where gb ~(Binding quant nm ty p _) = (quant, (nm,ty)):case p of
          Nothing -> []
          Just p -> gb $ case M.lookup p ctxt of 
            Nothing -> error $ "element "++show p++" not in map \n\twith ctxt: "++show ctx++" \n\t for bind: "++show bind++"\n\t"++s
            Just c -> c
            
checkContext _ c@(Context Nothing _ Nothing) = c
checkContext s ctx = ctx {- foldr seq ctx $ zip st ta
  where st = getBefore s (getTail ctx) ctx
        ta = getAfter s (getHead ctx) ctx -}




------------------------        
-- env with a context --        
------------------------
type WithContext = StateT Context Env 

getElm :: String -> Name -> WithContext (Either Binding Spine)
getElm s x = do
  ty <- lookupConstant x
  case ty of
    Nothing -> Left <$> (\ctxt -> lookupWith ("looking up "++x++"\n\t in context: "++show ctxt++"\n\t"++s) x ctxt) <$> ctxtMap <$> get
    Just a -> return $ Right a

-- | This gets all the bindings outside of a given bind and returns them in a list (not including that binding).
getBindings :: Binding -> WithContext [(Name,Type)]
getBindings bind = do
  ctx <- get
  return $ snd <$> getBefore "IN: getBindings" bind ctx
  
getAnExist :: WithContext (Maybe (Name,Type))
getAnExist = do
  ctx <- get
  let til = getTail ctx
      last = (elmQuant til, (elmName til, elmType til))
  return $ case ctx of
    Context _ _ Nothing -> Nothing
    _ -> snd <$> find (\(q,_) -> q == Exists) (last:getBefore "IN: getBindings" til ctx)
    
getForalls :: WithContext Constants
getForalls = do
  ctx <- ctxtMap <$> get
  return $ elmType <$> M.filter (\q -> elmQuant q == Forall) ctx
  
getExists :: WithContext Constants
getExists = do
  ctx <- ctxtMap <$> get
  return $ elmType <$> M.filter (\q -> elmQuant q == Exists) ctx

getAllBindings = do
  ctx <- get
  case ctx of
    Context _ _ Nothing -> return []
    _ -> (getBindings $ getTail ctx)


isolateForFail m = do
  s <- get
  c <- m
  case c of
    Nothing -> do
      put s
      return Nothing
    _ -> return c