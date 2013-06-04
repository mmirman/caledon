{-# LANGUAGE
 BangPatterns,
 ScopedTypeVariables
 #-}
module Src.Tracing where

import Debug.Trace
import System.IO.Unsafe
import Data.IORef

import Control.Exception
import Control.DeepSeq
import Data.Functor

{-# NOINLINE levelVar #-}
levelVar :: IORef Int
levelVar = unsafePerformIO $ newIORef 0

{-# NOINLINE level #-}
level = unsafePerformIO $ readIORef levelVar

vtrace !i | i < level = trace
vtrace !_ = const id

vtraceShow !_ !i2 s v | i2 < level = trace $ s ++" : "++show v
vtraceShow !i1 !_ s _ | i1 < level = trace s
vtraceShow !_ !_ _ _ = id

mtrace True = trace
mtrace False = const id



handlers :: [Handler (Either String a)]
handlers = [ Handler $ \(s :: ArithException)   -> return $ Left $ show s
           , Handler $ \(s :: ArrayException)   -> return $ Left $ show s
           , Handler $ \(s :: ErrorCall)        -> return $ Left $ show s
           , Handler $ \(s :: PatternMatchFail) -> return $ Left $ show s
           , Handler $ \(s :: SomeException)    -> return $ Left $ show s
           ]
           
deepAppendError :: NFData a => String -> a -> a
deepAppendError s a = case unsafePerformIO $ deepseq a (Right <$> return a) `catches` handlers of
  Left s' -> error $ s'++"\n"++s
  Right a -> a