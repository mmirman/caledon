module Src.FormulaSequence (Ctxt()) where

import Src.Context
import Src.AST
import qualified Data.Map as M
import Data.Sequence as S
import Data.Monoid
import qualified Data.Foldable as F

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
  
  getTy c (Con n) = snd $ ctxtConstants c M.! n
  getTy _ (Exi _ _ ty) = ty
  getTy c (DeBr i) = case i < height c of
    True  -> liftV i $ elemType $ index (ctxtContext c) i
    False -> error $ "WHAT? "++show i++"\nIN: "++show c
    
  getVal c (Con n) = case fst $ ctxtConstants c M.! n of
    Macro a -> a
    _ -> Pat $ Var $ Con n
  getVal c v = Pat $ Var v
  
  putTy c ty = c { ctxtHeight  = ctxtHeight c + 1 
                 , ctxtContext = B ty mempty <| ctxtContext c
                 }
  getTypes c = (ctxtConstants c, map elemType $ F.toList $ ctxtContext c)

instance Environment Ctxt where
  putLeft (c@Ctxt{ ctxtRecon = re, ctxtContext = seqe }) b = case viewl seqe of
    EmptyL -> c { ctxtRecon = Left b:re }
    a :< seqe ->  c { ctxtContext = a { elemRecon = Left b:elemRecon a} <| seqe }
  putRight b (c@Ctxt{ ctxtRecon = re, ctxtContext = seqe }) = case viewl seqe of
    EmptyL -> c { ctxtRecon = Right b:re }
    a :< seqe ->  c { ctxtContext = a { elemRecon = Right b:elemRecon a} <| seqe }
  
  rebuild (Ctxt{ ctxtRecon = re, ctxtContext = seqe }) b = rebuildFromRecon re $ F.foldl reb b seqe
    where reb f (B ty re) = case rebuildFromRecon re f of
                                 Done -> Done
                                 f -> Bind ty f

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
rebuildFromRecon (Left a:l) Done   = rebuildFromRecon l a
rebuildFromRecon (Right a:l) Done  = rebuildFromRecon l a
rebuildFromRecon (Left a:l) b      = rebuildFromRecon l (b :&: a)
rebuildFromRecon (Right a:l) b     = rebuildFromRecon l (a :&: b)
