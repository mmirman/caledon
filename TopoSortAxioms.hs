module TopoSortAxioms where

import AST

import Data.Graph
import qualified Data.Set as S

getVars val ty = filter (not . flip elem (map fst consts)) $ S.toList $ freeVariables val `S.union` freeVariables ty 

topoSortAxioms :: [(Name,Spine,Type)] -> [(Name,Spine,Type)]
topoSortAxioms axioms = map ((\((val,ty),n,_) -> (n,val,ty)) . v2nkel) vlst
  where (graph, v2nkel, k2v) = 
          graphFromEdges $ map (\(nm,val,ty) -> ((val,ty), nm , getVars val ty)) axioms
        -- note!  this doesn't check that there are no cycles!
        vlst = reverse $ topSort graph