{-# LANGUAGE BangPatterns, TupleSections #-} 
module TopoSortAxioms where

import AST

import Data.Graph
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Functor


seqList :: [a] -> (b -> b) 
seqList [] = id
seqList ((!_):l) = seqList l

finalizeList a = seqList a a

topoSort :: (a -> (Name,S.Set Name)) -> [a] -> [a]
topoSort producer scons = finalizeList $ map ((\(a,_,_) -> a) . v2nkel) $ topSort graph
  where res = finalizeList $ map (\a -> let (nm, e) = producer a in (a,nm,S.toList e)) scons
        (graph,v2nkel,_) = graphFromEdges res

topoSortComp producer scons = finalizeList $ map ((\(a,_,_) -> a) . v2nkel) $ topSort graph
  where res = finalizeList $ map (\a -> let (nm, e) = producer a in (a,nm,S.toList e)) scons
        (graph',v2nkel,_) = graphFromEdges res
        graph = transposeG graph'

hasNoCycles graph = all isAcyc $ stronglyConnComp graph'
  where graph' = (\(a,b) -> ((), a , b)) <$> M.toList (S.toList <$> graph)
        
        isAcyc (AcyclicSCC _) = True
        isAcyc _ = False