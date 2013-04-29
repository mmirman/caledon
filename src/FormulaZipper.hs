module Src.FormulaZipper (Ctxt()) where

import Src.Context
import Src.AST
import qualified Data.Map as M

repeate 0 a = id
repeate 1 f = f
repeate n f = f . repeate (n-1) f

data FZipper = Top
             | L FZipper Form 
             | R Form FZipper 
             | B FZipper Type
             deriving (Show)
                   
data Ctxt = Ctxt { ctxtConstants :: Constants
                 , ctxtHeight    :: Int
                 , ctxtContext   :: FZipper
                 } deriving (Show)

instance Context Ctxt where
  emptyCon cons = Ctxt { ctxtConstants = cons
                       , ctxtHeight    = 0
                       , ctxtContext   = Top
                       } 
  
  getTy c (Con n) = ctxtConstants c M.! n
  getTy _ (Exi i nm ty) = ty
  getTy c (DeBr i) = case repeate i up $ upZero $ ctxtContext c of
    B _ ty -> liftV i $ ty
    Top -> error $ "WHAT? "++show i++"\nIN: "++show c
    
  putTy c ty = c { ctxtHeight  = ctxtHeight c + 1 
                 , ctxtContext = B (ctxtContext c) ty
                 } 
               
  height = ctxtHeight

instance Environment Ctxt where
  putLeft c b = c { ctxtContext = L (ctxtContext c) b }
  putRight b c = c { ctxtContext = R b (ctxtContext c) }
  
  rebuild c b = rebuildForm (ctxtContext c) b

  upI i (Ctxt cons j c) b = case upDone i (c,b) of
    Just (ctxt,b) -> Just (Ctxt cons (j - i) ctxt, b)
    Nothing -> Nothing
    
    


upZero (L c f) = upZero c
upZero (R f c) = upZero c
upZero t = t

up (L c f) = up c
up (R f c) = up c
up (B c _) = upZero c
up t = t

upWithZero l Done = case l of
  L c f -> upWithZero c f
  R f c -> upWithZero c f
  _ -> (l, Done)
upWithZero (L c f) ctxt = upWithZero c $ ctxt :&: f
upWithZero (R f c) ctxt = upWithZero c $ f :&: ctxt
upWithZero t l = (t,l)

upWith l Done = case l of
  L c f -> upWith c f
  R f c -> upWith c f
  B c _ -> upWithZero c Done
  Top -> (Top, Done)
upWith (L c f) ctxt = upWith c $ ctxt :&: f
upWith (R f c) ctxt = upWith c $ f :&: ctxt
upWith (B c ty) ctxt = upWithZero c $ Bind ty ctxt
upWith Top ctxt = (Top, ctxt)

upDone i (a,b) = upDone' i (upWithZero a b)
  where upDone' (-1) (ctxt,Done) = Nothing
        upDone' (-1) (ctxt,nxt)  = Just (ctxt,nxt)
        upDone' i (ctxt,nxt) = upDone' (i-1) (upWith ctxt nxt)
  
rebuildForm a Done = rebuildTop a
  where rebuildTop (B c t) = rebuildTop c
        rebuildTop (L c t) = rebuildForm c t
        rebuildTop (R t c) = rebuildForm c t
        rebuildTop Top = Done
rebuildForm (B c t) h = rebuildForm c $ Bind t h
rebuildForm (L c t) h = rebuildForm c $ h :&: t
rebuildForm (R t c) h = rebuildForm c $ t :&: h
rebuildForm Top h = h
