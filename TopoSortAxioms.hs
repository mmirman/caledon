{-# LANGUAGE BangPatterns #-} 
module TopoSortAxioms where

import AST

import Data.Graph
import qualified Data.Set as S
getVars val ty = concatMap (\nm -> [nm,"#v:"++nm])
               $ filter (not . flip elem (map fst consts)) 
               $ S.toList $ freeVariables val `S.union` freeVariables ty 

topoSortAxioms :: [(Maybe Name, (Bool,Integer,Bool), Name,Term,Type)] -> [(Maybe Name, (Bool,Integer,Bool), Name,Term,Type)]
topoSortAxioms axioms = map ((\((fam,s,val,ty),n,_) -> (fam,s,n,val,ty)) . v2nkel) vlst
  where (graph, v2nkel, _) = 
          graphFromEdges $ map (\(fam,s,nm,val,ty) -> ((fam,s,val,ty), nm , getVars val ty)) axioms
        -- note!  this doesn't check that there are no cycles!
        vlst = reverse $ topSort graph
        

seqList :: [a] -> (b -> b) 
seqList [] = id
seqList ((!_):l) = seqList l

finalizeList a = seqList a a

topoSort :: (a -> (Name,S.Set Name)) -> [a] -> [a]
topoSort producer scons = finalizeList $ map ((\(a,_,_) -> a) . v2nkel) $ topSort graph
  where res = finalizeList $ map (\a -> let (nm, e) = producer a in (a,nm,S.toList e)) scons
        (graph,v2nkel,_) = graphFromEdges res
