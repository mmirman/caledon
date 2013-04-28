{-# LANGUAGE BangPatterns, TupleSections #-} 
module TopoSortAxioms where

import AST

import Data.Graph
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Functor
import Data.Monoid
import Data.Maybe

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

data Order = Name :<=: Name
           | Name :<: Name
           deriving (Eq, Show)
                                                     
makeGraph = foldr (\(nm,l) gr -> case M.lookup nm gr of 
                      Nothing -> M.insert nm (S.singleton l) gr
                      Just r -> M.insert nm (S.insert l r) gr) mempty 

isUniverseGraph :: [Order] -> Bool
isUniverseGraph lst = all isAcyc $ stronglyConnComp graph' 
  where make (a :<=: b) = (a , b)
        make (a :<: b) = (a , b)
        graph' = (\(a,b) -> (a, a , b)) <$> M.toList (S.toList <$> makeGraph (make <$> lst))
                                                          
        isLessThan (_ :<: _) = True
        isLessThan _ = False
        
        someGraph = makeGraph $ make <$> filter isLessThan lst
        
        isAcyc (AcyclicSCC _) = True
        isAcyc (CyclicSCC sames) = all noOverlap sames
          where noOverlap x = S.null $ S.intersection (fromMaybe mempty $ M.lookup x someGraph) (S.fromList sames)
                                                                                                                                                                                                               