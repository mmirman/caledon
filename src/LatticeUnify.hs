module Src.LatticeUnify where

import Names
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.NodeMap
import Data.Graph.Inductive.Query.DFS

data ConsGraph = ConsGraph { posGraph :: Gr Name () 
                           , negGraph :: Gr Name ()
                           , nodeMap  :: NodeMap Name
                           } 
                 
connected gr s l = case lab gr (fst s) of
  Nothing -> False
  _ -> elem (fst l) $ reachable (fst s) gr

insertNode gr s = case lab gr (fst s) of
  Nothing -> insNode s gr
  _ -> gr

insert gr s l = ins $ insertNode (insertNode gr s) l
  where ins gr = if elem (fst l) $ neighbors gr (fst l)
                 then gr
                 else insEdge (fst s, fst l, ()) gr 

insLTE (ConsGraph pos neg nm) s l = 
  let (s',nm')  = mkNode nm s
      (l',nm'') = mkNode nm' l
  in if not $ connected neg s' l' 
     then return $ ConsGraph (insert pos s' l') neg nm''
     else error $ s++" ≤ "++l
          
insLT (ConsGraph pos neg nm) s l = 
  let (s',nm') = mkNode nm s
      (l',nm'') = mkNode nm' l
  in if not $ connected pos l' s'
     then return $ ConsGraph (insert pos s' l') (insert neg l' s') nm''
     else error $ s++" < "++l

newGraph = ConsGraph empty empty new


testGraph = do
  Just ()
  let gr = newGraph
      
  gr <- insLT gr "a" "b"
  gr <- insLTE gr "a" "b"
  gr <- insLTE gr "b" "c"
  gr <- insLTE gr "c" "b"
  gr <- insLT gr "c" "d"
  gr <- insLTE gr "d" "c"

  Just ()