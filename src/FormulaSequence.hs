module Src.FormulaSequence (Ctxt()) where

import Src.Context
import Src.AST
import qualified Data.Map as M
import Data.Sequence as S
import Data.Monoid
import qualified Data.Foldable as F
import qualified Data.List as L
import Debug.Trace

type Recon = [Either Form Form]

data Elem = B { elemType :: Type
              , elemRecon :: Recon
              } 
          deriving (Show)
                   
data Ctxt = Ctxt { ctxtConstants :: !Constants
                 , ctxtHeight    :: !Int
                 , ctxtRecon     :: Recon
                 , ctxtContext   :: Seq Elem
                 } deriving (Show)

instance Context Ctxt where
  emptyCon cons = Ctxt { ctxtConstants = cons
                       , ctxtHeight    = 0
                       , ctxtRecon     = mempty
                       , ctxtContext   = mempty
                       }
  
  height = ctxtHeight  
  getTy c (Con n) | isUniverse (Var $ Con n) = universe
  getTy c (Con n) = snd $ case M.lookup n $ ctxtConstants c of
    Just i -> i
    Nothing -> error $ show n ++" not found in the context."
  getTy _ (Exi _ _ ty) = ty
  getTy c (DeBr i) = case i < height c of
    True  -> liftV i $ elemType $ index (ctxtContext c) i
    False -> error $ "WHAT? "++show i++"\nIN: "++show c
    
  getVal c (Con n) = case fst $ ctxtConstants c M.! n of
    Macro a -> a -- we shouldn't need to lift because this is coming from constants
    _ -> Pat $ Var $ Con n
  getVal c v = Pat $ Var v
  
  putTy c ty = c { ctxtHeight  = ctxtHeight c + 1 
                 , ctxtContext = B ty mempty <| ctxtContext c
                 }
  getTypes c = (ctxtConstants c, map elemType $ F.toList $ ctxtContext c)

toLeft (Left _) = True
toLeft _ = False

reset (Ctxt cons 0 recon ctxt,f) = (Ctxt cons 0 [] ctxt, rebuildFromRecon recon f)
reset (a,f) = case upI 1 a f of
    Nothing -> (emptyCon $ ctxtConstants a, rebuildFromRecon (ctxtRecon a) f)
    Just a  -> a
    
instance Environment Ctxt where
  isDone (Ctxt{ctxtHeight = 0, ctxtRecon = []}) = True
  isDone _ = False
  
  nextUp (Ctxt cons 0 recon ctxt,f) = (Ctxt cons 0 [] ctxt, rebuildFromRecon recon f)
  nextUp (Ctxt cons h ro ctxt,b) = case viewl ctxt of
    EmptyL -> (emptyCon cons, rebuildFromRecon ro b)
    B ty ro' :< ctxt' -> (Ctxt cons (h-1) ro ctxt', bind ty $ rebuildFromRecon ro' b)

  viewLeft (ctxt@Ctxt{ ctxtContext = seqe, ctxtRecon = recon } , form) = case viewl seqe of
    EmptyL -> do 
      ~(form',recon') <- bR recon 
      return (ctxt { ctxtRecon = recon' } , form' )
    B ty recon :< seqe -> do
      ~(form',recon') <- bR recon 
      return (ctxt { ctxtContext = B ty recon' <| seqe } , form' )
    where bR recon = case L.partition toLeft recon of
            ([],_) -> Nothing
            (lefts,rights) -> Just (foldr mappend Done $ map (\(Left a) -> a) lefts , Right form:rights) 

  viewRight (ctxt@Ctxt{ ctxtContext = seqe, ctxtRecon = recon } , form) = case viewl seqe of
    EmptyL -> do 
      (form',recon') <- bR recon 
      return (ctxt { ctxtRecon = recon' } , form' )
    B ty recon :< seqe -> do
      (form',recon') <- bR recon 
      return (ctxt { ctxtContext = B ty recon' <| seqe } , form' )
    where bR recon = case L.partition toLeft recon of
            ([],_) -> Nothing
            (lefts,rights) -> Just (foldl mappend Done $ map (\(Right a) -> a) rights , Left form:lefts)             
            
  putLeft (c@Ctxt{ ctxtRecon = re, ctxtContext = seqe }) b = case viewl seqe of
    EmptyL -> c { ctxtRecon = Left b:re }
    a :< seqe ->  c { ctxtContext = a { elemRecon = Left b:elemRecon a} <| seqe }
  putRight b (c@Ctxt{ ctxtRecon = re, ctxtContext = seqe }) = case viewl seqe of
    EmptyL -> c { ctxtRecon = Right b:re }
    a :< seqe ->  c { ctxtContext = a { elemRecon = Right b:elemRecon a} <| seqe }
  
  rebuild (Ctxt{ ctxtRecon = re, ctxtContext = seqe }) b = rebuildFromRecon re $ F.foldl reb b seqe
    where reb f (B ty re) = bind ty $ rebuildFromRecon re f

  upI i (Ctxt _ h _ _) _ | i > h = error "context is not large enough"
  upI i (Ctxt cons h ro ctxt) b = case S.splitAt i ctxt of
    (lower, upper) -> case viewl upper of
      EmptyL -> if b == Done && reb == Done then Nothing else Just (emptyCon cons, reb)
        where reb = rebuild (Ctxt cons i ro lower) b
      B ty re :< ctxt' -> if b == Done && reb == Done then Nothing else Just (newC, reb) 
        where reb = rebuild (Ctxt cons i re lower) b
              newC = Ctxt cons (h - i) ro $ B ty [] <| ctxt'

-- tail call optimized beauty?  Its naturally that way!
rebuildFromRecon :: Recon -> Form -> Form
rebuildFromRecon [] a              = a
rebuildFromRecon (Left a:l) b      = rebuildFromRecon l (b `mappend` a)
rebuildFromRecon (Right a:l) b     = rebuildFromRecon l (a `mappend` b)
