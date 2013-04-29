module Src.Variables where

import Data.Functor
import Control.Monad.State.Class (MonadState(), get, modify)

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
getNewWith s = (++s) <$> getNew