module TopoSortAxioms where

import AST

import Data.Graph
import qualified Data.Set as S
getVars val ty = concatMap (\nm -> [nm,"#v:"++nm])
               $ filter (not . flip elem (map fst consts)) 
               $ S.toList $ freeVariables val `S.union` freeVariables ty 

topoSortAxioms :: [(Maybe Name, Name,Term,Type)] -> [(Maybe Name, Name,Term,Type)]
topoSortAxioms axioms = map ((\((fam,val,ty),n,_) -> (fam,n,val,ty)) . v2nkel) vlst
  where (graph, v2nkel, k2v) = 
          graphFromEdges $ map (\(fam,nm,val,ty) -> ((fam,val,ty), nm , getVars val ty)) axioms
        -- note!  this doesn't check that there are no cycles!
        vlst = reverse $ topSort graph