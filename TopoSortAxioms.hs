{-# LANGUAGE BangPatterns, TupleSections #-} 
module TopoSortAxioms where

import AST
import Names
import Substitution
import Data.Graph
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Functor
import Data.Monoid
import Data.Maybe
import Control.Lens hiding (Choice(..))

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

data Order = !Name :<=: !Name
           | !Name :<:  !Name
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



topoSortAxioms :: Bool -> [FlatPred] -> [FlatPred]
topoSortAxioms accountPot axioms = topoSortComp (\p -> (p^.predName,) 
                                                       -- unsound can mean this causes extra cyclical things to occur
                                                       $ (if accountPot && p^.predSound then S.union (getImplieds $ p^.predName) else id)
                                                       $ S.fromList 
                                                       $ filter (not . flip elem (map fst consts)) 
                                                       $ S.toList $ freeVariables p ) axioms
                        
  where nm2familyLst  = catMaybes $ (\p -> (p^.predName,) <$> (p^.predFamily)) <$> axioms
        
        family2nmsMap = foldr (\(fam,nm) m -> M.insert nm (case M.lookup nm m of
                                  Nothing -> S.singleton fam
                                  Just s -> S.insert fam s) m
                                )  mempty nm2familyLst
        
        family2impliedsMap = M.fromList $ (\p -> (p^.predName, 
                                                  mconcat 
                                                  $ catMaybes 
                                                  $ map (`M.lookup` family2nmsMap) 
                                                  $ S.toList 
                                                  $ S.union (getImpliedFamilies $ p^.predType) (fromMaybe mempty $ freeVariables <$> p^.predValue)
                                                 )) <$> axioms
        
        getImplieds nm = fromMaybe mempty (M.lookup nm family2impliedsMap)
        
getImpliedFamilies s = S.intersection fs $ gif s
  where fs = freeVariables s
        gif (Spine "#imp_forall#" [ty,a]) = (case getFamilyM ty of
          Nothing -> id
          Just f | f == tipeName -> id
          Just f -> S.insert f) $ gif ty `S.union` gif a 
        gif (Spine a l) = mconcat $ gif <$> l
        gif (Abs _ ty l) = S.union (gif ty) (gif l)
