{-# LANGUAGE DeriveFunctor #-}

module Choice where
import Control.Monad
import Data.Functor
import Control.Applicative
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe

data Choice a = Choice a :<|>: Choice a 
              | Fail
              | Success a
              deriving (Functor)

instance Monad Choice where 
  return = Success
  Fail >>= _ = Fail
  (m :<|>: m') >>= f = (m >>= f) :<|>: (m' >>= f)
  Success a >>= f = f a

instance Applicative (Choice) where  
  pure = Success
  mf <*> ma = mf >>= (<$> ma)
  
instance Alternative (Choice) where
  empty = Fail
  (<|>) = (:<|>:)
        
instance MonadPlus (Choice) where        
  mzero = Fail
  mplus = (:<|>:)
  
  
class RunChoice m where  
  runChoice :: m a -> Maybe a
  
instance RunChoice Choice where
  runChoice chs = case dropWhile notSuccess lst of
    [] -> Nothing
    (Success a):l -> Just a
    _ -> error "this result makes no sense"
    where lst = chs:concatMap to lst
          to Fail = []
          to (a :<|>: b) = [a,b]
          to a = [a]
        
          notSuccess (Success a) = False
          notSuccess _ = True
instance RunChoice Maybe where runChoice = id