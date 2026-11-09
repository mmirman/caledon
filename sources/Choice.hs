{-# LANGUAGE
 DeriveFunctor,
 FlexibleContexts,
 TypeSynonymInstances,
 FlexibleInstances,
 MultiParamTypeClasses
 #-}

module Choice where

import Control.Monad
import Data.Functor ((<$>), (<$))
import Data.Char (isSpace)
import Control.Applicative
import Control.Monad.Error.Class (catchError, throwError, MonadError)
import Control.Monad.Cont
import Control.Monad.Trans (lift)

data Choice a = Choice a :<|>: Choice a
              | Fail String
              | Success a
              deriving (Functor)

instance Monad Choice where
  Fail a >>= _ = Fail a
  (m :<|>: m') >>= f = (m >>= f) :<|>: (m' >>= f)
  Success a >>= f = f a

instance MonadFail Choice where
  fail = Fail

instance Applicative Choice where
  pure = Success
  mf <*> ma = mf >>= (<$> ma)

-- Keep alternatives until their entire continuation has succeeded. Running
-- runError here commits to a local success and destroys both backtracking
-- and the fairness of the breadth-first interpreter.
determine = (:<|>:)

-- An explicit cut, for boundaries where a complete result has been checked.
-- Keep this separate from Alternative and error annotation: those must not
-- silently discard branches whose later constraints have yet to be solved.
once :: Choice a -> Choice a
once search = either Fail Success (runError search)

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
      _ -> Left "No solution"
    Success a : _ -> Right a
    _ -> error "this result makes no sense"
    where lst = chs:queue lst 1

          queue _ 0 = []
          queue [] _ = error "queue size should be empty when queue is empty"
          queue ((a :<|>: b):l) q = a:b:queue l (q + 1)
          queue (_:l) q = queue l (q - 1)

          notFail (Fail s) = all isSpace s
          notFail _ = True

          notSuccess (Success _) = False
          notSuccess _ = True

appendErr :: (MonadError String m) => String -> m a -> m a
appendErr s m = catchError m $ \s' ->
  throwError $ if all isSpace s' then s' else s' ++ "\n" ++ s

instance MonadError String Choice where
  throwError = Fail
  catchError (Fail s) handler = handler s
  catchError (Success a) _ = Success a
  catchError (a :<|>: b) handler =
    catchError a handler :<|>: catchError b handler

type CONT_T a m c = ((c -> m a) -> m a)

-- why doesn't this exist in the standard library?
instance (Monad m, Alternative m) => Alternative (ContT a m) where
  empty = lift $ empty
  c1 <|> c2 = ContT $ \cont -> m1f cont <|> m2f cont
    where m1f = runContT c1
          m2f = runContT c2

