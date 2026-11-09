-- | Inferred predicative universe levels. An edge a -> b has weight zero
-- for a <= b, and weight one for a < b. Levels are natural numbers.
module Universe (Order(..), solveUniverses, isUniverseGraph) where

import Names
import Control.Monad (forM_)
import Data.Array (Array, array, accumArray, (!))
import Data.Array.ST (runSTArray, newArray, readArray, writeArray)
import qualified Data.Graph as G
import Data.Tree (flatten)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

data Order = !Name :<=: !Name
           | !Name :<: !Name
           deriving (Eq, Show)

-- | Return the pointwise least satisfying assignment. A solution exists
-- exactly when no strongly connected component contains a strict edge.
-- Collapse the zero-weight SCCs, then compute longest paths in the DAG.
-- The graph work is O(V+E), with O((V+E) log V) name indexing, O(V+E) space.
-- There is no arbitrary upper bound on the inferred universe levels.
solveUniverses :: [Order] -> Maybe (M.Map Name Integer)
solveUniverses constraints
  | any strictCycle edges = Nothing
  | otherwise = Just $ M.fromDistinctAscList
      [(name, levels ! (component ! v)) | (name,v) <- M.toAscList ids]
  where
    namedEdges = map edge constraints
    edge (a :<=: b) = (a, b, 0)
    edge (a :<: b) = (a, b, 1)
    names = S.toAscList $ S.fromList [v | (a,b,_) <- namedEdges, v <- [a,b]]
    ids = M.fromDistinctAscList $ zip names [0..]
    bounds = (0, M.size ids - 1)
    edges = [(ids M.! a, ids M.! b, w) | (a,b,w) <- namedEdges]
    graph = G.buildG bounds [(a,b) | (a,b,_) <- edges]
    components = map flatten (G.scc graph)
    component = array bounds [(v,i) | (i,vs) <- zip [0..] components, v <- vs]
    strictCycle (a,b,w) = w == 1 && component ! a == component ! b
    cbounds = (0, length components - 1)
    dagEdges = [(component ! a, component ! b, w) | (a,b,w) <- edges,
                component ! a /= component ! b]
    dag = G.buildG cbounds [(a,b) | (a,b,_) <- dagEdges]
    outgoing :: Array Int [(Int,Integer)]
    outgoing = accumArray (flip (:)) [] cbounds [(a,(b,w)) | (a,b,w) <- dagEdges]
    levels = runSTArray $ do
      result <- newArray cbounds 0
      forM_ (G.topSort dag) $ \a -> do
        level <- readArray result a
        forM_ (outgoing ! a) $ \(b,w) -> do
          old <- readArray result b
          writeArray result b $! max old (level + w)
      return result

isUniverseGraph :: [Order] -> Bool
isUniverseGraph = maybe False (const True) . solveUniverses
