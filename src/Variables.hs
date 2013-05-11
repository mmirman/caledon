{-# LANGUAGE FlexibleContexts #-}
module Src.Variables where

import Control.Monad.State.Class

getNewWith :: MonadState Int m => String -> m String
getNewWith s = do
  i <- get
  put (i + 1)
  return $ show i ++ s

