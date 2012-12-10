{-# LANGUAGE 
 DeriveFunctor, 
 FlexibleContexts,
 TypeSynonymInstances,
 FlexibleInstances,
 MultiParamTypeClasses
 #-}

module Choice where
import Control.Monad
import Data.Functor
import Control.Applicative
import Control.Monad.Error.Class (catchError, throwError, MonadError)
import Control.Monad.State.Class

data Choice a = Choice a :<|>: Choice a 
              | Fail String
              | Success a
              deriving (Functor)

instance Monad Choice where 
  fail a = Fail a
  return = Success
  Fail a >>= _ = Fail a
  (m :<|>: m') >>= f = (m >>= f) :<|>: (m' >>= f)
  Success a >>= f = f a
  
instance Applicative Choice where  
  pure = Success
  mf <*> ma = mf >>= (<$> ma)
  
instance Alternative Choice where
  empty = Fail ""
  (<|>) = (:<|>:)
        
instance MonadPlus Choice where        
  mzero = Fail ""
  mplus = (:<|>:)
  
class RunChoice m where  
  runError :: m a -> Either String a
  
instance RunChoice Choice where
  runError chs = case dropWhile notSuccess lst of
    [] -> case dropWhile notFail lst of 
      Fail a:_ -> Left a
      _ -> error "this result makes no sense"
    (Success a):_ -> Right a
    _ -> error "this result makes no sense"
    where lst = chs:queue lst 1
          
          queue _ 0 = []
          queue [] _ = error "queue size should be empty when queu is empty"
          queue ((a :<|>: b):l) q = a:b:queue l (q + 1)
          queue (_:l) q = queue l (q - 1)
          
          notFail (Fail _) = False
          notFail _ = True
          
          notSuccess (Success _) = False
          notSuccess _ = True
  
appendErr :: (MonadError String m) => String -> m a -> m a
appendErr s m = catchError m $ \s' -> throwError $ s' ++ "\n" ++ s
  
instance MonadError String Choice where
  throwError a = Fail a
  catchError try1 foo_try2 = case runError try1 of
    Left s -> foo_try2 s
    Right a -> Success a

getNew :: (MonadState Integer m) => m String
getNew = do 
  st <- get
  let n = 1 + st
  put n
  return $! show n