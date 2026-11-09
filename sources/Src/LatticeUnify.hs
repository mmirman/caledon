{-# LANGUAGE FlexibleContexts #-}
module Src.LatticeUnify (ConsGraph, newGraph, insLT, insLTE, validateGraph) where

import Names
import Universe
import Control.Monad.Except (MonadError, throwError)

newtype ConsGraph = ConsGraph [Order] deriving (Eq, Show)

newGraph :: ConsGraph
newGraph = ConsGraph []

-- Accumulate edges in O(1); validate once at the end of a candidate
-- unification branch. Re-solving on every insertion is quadratic.
insertConstraint :: Monad m => ConsGraph -> Order -> m ConsGraph
insertConstraint (ConsGraph constraints) constraint =
  return $ ConsGraph (constraint : constraints)

validateGraph :: MonadError String m => ConsGraph -> m ()
validateGraph (ConsGraph constraints)
  | isUniverseGraph constraints = return ()
  | otherwise = throwError $ "Inconsistent universe constraints: " ++ show constraints

insLTE :: MonadError String m => ConsGraph -> Name -> Name -> m ConsGraph
insLTE graph a b = insertConstraint graph (a :<=: b)

insLT :: MonadError String m => ConsGraph -> Name -> Name -> m ConsGraph
insLT graph a b = insertConstraint graph (a :<: b)
