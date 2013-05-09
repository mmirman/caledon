{-# LANGUAGE 
 BangPatterns,
 FlexibleContexts
 #-}
module Src.Pipeline(typeCheckAll) where



import AST
import TopoSortAxioms
import Choice

import Src.Variables
import qualified Src.AST as A
import Src.Elaborate
import Src.HOU
import Src.Reconstruction
import Src.Tracing
import Src.Translate
import Src.Variables

import Control.Applicative 
import Control.Lens hiding (Choice(..))
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.State (runStateT)
import Control.Monad.State.Class (MonadState())

import Data.Foldable (foldrM)
import Data.Monoid

import Debug.Trace
import Debug.Trace

import qualified Data.Map as M


impurePutStrLn True s = return $! trace s $ ()
impurePutStrLn False s = return ()


inferAxiom verb (!name,st,!tmOrg,!tyOrg) (!graph , !constants) = do

  impurePutStrLn verb $ "Elaborating:"
  impurePutStrLn verb $ name++"  : "++show tmOrg
  impurePutStrLn verb $ " :: "++show tyOrg
  
  !tm <- return $! fromSpine tmOrg
  !ty <- return $! A.fromType $! fromSpine tyOrg
  
  v <- getNewWith "@tipe"
  
  (!ty   ,  constraints) <- typeConstraints constants (A.Pat ty) (A.tipemake v)
  impurePutStrLn verb $ "Constraints: " ++show constraints
  (graph , !recon)       <- unifyAll graph constants constraints
  !ty <- return $! A.fromType $!
         quantifyExistentials $! substReconstruct recon ty
         
  (!tm   ,  constraints) <- typeConstraints constants tm ty

  (graph , !recon)       <- unifyAll graph constants constraints
  

  
  !tm <- return $! 
         quantifyExistentials $! substReconstruct recon tm
  !constants <- return $! 
                M.insert name (case st of 
                                  Just (sequential,i) -> (A.Axiom sequential i,A.fromType tm)
                                  Nothing -> (A.Macro tm, ty)
                              ) constants
  
  impurePutStrLn verb $ "Result:"
  impurePutStrLn verb $ name++" : "++show (toSpine tm)++"\n"
  
  return $! (graph, constants)

pipeline verbose nttLst = do
  let bundle (FlatPred (PredData _ seqi i _) nm tm ty ki) = case tm of
        Just tm -> (nm,Just (seqi,fromIntegral i),tm,ty)
        Nothing -> (nm,Nothing,ty,ki)
        
      axioms = map bundle $ reverse $ topoSortAxioms True nttLst
  s <- getNew
  s <- getNew
  
  (graph,!constants) <- foldrM (inferAxiom verbose) (newGraph, A.constants) axioms
  
  return constants


typeCheckAll :: Bool -> [Decl] -> Choice [Decl]
typeCheckAll verbose preds = do
  
  constants <- pipeline verbose $ toAxioms True preds
  
  let constList = M.toList constants
      valMap = M.fromList 
               $ concatMap (\(nm,a) -> case a of
                               (A.Macro val,_) -> [(nm,toSpine val)]
                               _ -> []
                           ) constList
      tyMap  = (toSpine . A.Pat . snd) <$> constants
  
  let newPreds (Predicate t nm _ cs) = Predicate t nm (tyMap M.! nm) $ map (\(b,(nm,_)) -> (b,(nm, tyMap M.! nm))) cs
      newPreds (Query nm _) = Query nm (tyMap M.! nm)
      newPreds (Define t nm _ _) = Define t nm (valMap M.! nm) (tyMap M.! nm)
  
  return $ newPreds <$> preds

toAxioms :: Bool -> [Decl] -> [FlatPred]
toAxioms b = concat . zipWith toAxioms' [1..]
  where toAxioms' j (Predicate s nm ty cs) = 
          (FlatPred (PredData (Just $ tipeName) False j s) nm Nothing ty tipe)
          :zipWith (\(sequ,(nm',ty')) i -> (FlatPred (PredData (Just nm) sequ i False) nm' Nothing ty' tipe)) cs [0..]
        toAxioms' j (Query nm val) = [(FlatPred (PredData Nothing False j False) nm Nothing val tipe)]
        toAxioms' j (Define s nm val ty) = [ FlatPred (PredData Nothing False j s) nm (Just val) ty tipe]
  

reduceDecsByName :: [Decl] -> [Decl]
reduceDecsByName decs = map snd $ M.toList $ M.fromList $ map (\a -> (a ^. declName,a)) decs

