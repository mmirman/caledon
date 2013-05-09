
module Src.Variables where

import Data.Functor

import System.IO.Unsafe
import Data.IORef

currVar = unsafePerformIO $ newIORef 0

unsafeGetNewVar a = unsafePerformIO $ case a of
  () -> atomicModifyIORef currVar $ \a -> (a + 1, (show a))

getNew :: (Monad m) => m String
getNew = return $ unsafeGetNewVar ()
  
getNewWith :: (Functor f, Monad f) => String -> f String
getNewWith s = (++s) <$> getNew



