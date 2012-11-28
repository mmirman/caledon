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
import Control.Monad.Error (ErrorT, runErrorT)
import Control.Monad.Error.Class (catchError, throwError, MonadError)
import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Data.Maybe

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
    where lst = chs:to lst 1
          
          to l 0 = []
          to ((a :<|>: b):l) q = a:b:to l (q + 1)
          to (_:l) q = to l (q - 1)
          
          notFail (Fail a) = False
          notFail _ = True
          
          notSuccess (Success a) = False
          notSuccess _ = True
          
type Error = ErrorT String Identity

instance RunChoice Error where 
  runError = runIdentity . runErrorT
  
appendErr :: (MonadError String m) => String -> m a -> m a
appendErr s m = catchError m $ \s' -> throwError $ s' ++ "\n" ++ s
  
instance MonadError String Choice where
  throwError a = Fail a
  catchError try1 foo_try2 = case runError try1 of
    Left s -> foo_try2 "no error given"
    Right a -> Success a