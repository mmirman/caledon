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
import Control.Monad.Cont

data Choice a = Choice a :<|>: Choice a
              | Fail String
              | Success a
              deriving (Functor)

instance Monad Choice where
  fail = Fail
  return = Success
  Fail a >>= _ = Fail a
  (m :<|>: m') >>= f = (m >>= f) :<|>: (m' >>= f)
  Success a >>= f = f a

instance Applicative Choice where
  pure = Success
  mf <*> ma = mf >>= (<$> ma)

--determine a b = appendErr "" $ (:<|>:) (appendErr "" a) (appendErr "" b)
determine = (:<|>:)

instance Alternative Choice where
  empty = Fail ""
  (<|>) = determine

instance MonadPlus Choice where
  mzero = Fail ""
  mplus = determine

class RunChoice m where
  runError :: m a -> Either String a

instance RunChoice Choice where
  runError chs = case dropWhile notSuccess lst of
    [] -> case dropWhile notFail lst of
      Fail a:_ -> Left a
      _ -> error "this result makes no sense"
    Success a : _ -> Right a
    _ -> error "this result makes no sense"
    where lst = chs:queue lst 1

          queue _ 0 = []
          queue [] _ = error "queue size should be empty when queue is empty"
          queue ((a :<|>: b):l) q = a:b:queue l (q + 1)
          queue (_:l) q = queue l (q - 1)

          notFail (Fail _) = False
          notFail _ = True

          notSuccess (Success _) = False
          notSuccess _ = True

appendErr :: (MonadError String m) => String -> m a -> m a
appendErr s m = catchError m $ \s' -> throwError $ s' ++ "\n" ++ s

instance MonadError String Choice where
  throwError = Fail
  catchError try1 foo_try2 = case runError try1 of
    Left s -> foo_try2 s
    Right a -> Success a

type CONT_T a m c = ((c -> m a) -> m a)

-- why doesn't this exist in the standard library?
instance (Monad m, Alternative m) => Alternative (ContT a m) where
  empty = lift $ empty
  c1 <|> c2 = ContT $ \cont -> m1f cont <|> m2f cont
    where m1f = runContT c1
          m2f = runContT c2
    