module TopoSortAxioms where

import AST

import Data.Graph
import qualified Data.Set as S

getVars = filter (not . flip elem (map fst consts)) . S.toList . freeVariables

topoSortAxioms :: [(Name,Type)] -> [(Name,Type)]
topoSortAxioms axioms = map ((\(ty,n,_) -> (n,ty)) . v2nkel) vlst
  where (graph, v2nkel, k2v) = graphFromEdges $ map (\(nm,ty ) -> (ty, nm , getVars ty)) axioms
        -- note!  this doesn't check that there are no cycles!
        vlst = reverse $ topSort graph