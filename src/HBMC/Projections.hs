{-# LANGUAGE RecordWildCards #-}
module HBMC.Projections where

import Text.Show.Pretty (ppShow)
import Control.Applicative( (<$>), (<*>) )

import Tip.Pretty
import Tip.Pretty.SMT ()

import Tip.Fresh

import Tip.Core

import HBMC.Data

import HBMC.Identifiers

projectPatterns :: DataInfo Var -> Theory Var -> Fresh (Theory Var)
projectPatterns di Theory{..}
  = do fns <- sequence
         [ do body <- projectExpr di func_body
              return Function{func_body=body,..}
         | Function{..} <- thy_funcs ]
       return Theory{thy_funcs=fns,..}

projExpr :: (Type Var,Int) -> Expr Var -> Expr Var
projExpr (t,i) e = Gbl (Global (proj t i) (PolyType [] [exprType e] t) []) :@: [e]

projectExpr :: DataInfo Var -> Expr Var -> Fresh (Expr Var)
projectExpr di = go
 where
  go e0 =
    case e0 of
      Match e alts ->
        letExpr e $ \ lx ->
           Match (Lcl lx) <$>
             sequence
               [ case pat of
                   Default -> Case Default <$> go rhs
                   ConPat k vars
                     -> do let ps = projs_of_con di k
                           rhs' <-
                             substMany
                               [ (v,projExpr p (Lcl lx))
                               | (v,p) <- vars `zip` ps
                               ]
                               rhs
                           Case (ConPat k []) <$> go rhs'
                   _ -> error $ "projectPatterns: \n" ++ ppRender e0
               | Case pat rhs <- alts
               ]
      hd :@: args -> (hd :@:) <$> mapM go args
      Lam args e  -> Lam args <$> go e
      Let l e1 e2 -> Let l <$> go e1 <*> go e2
      Quant qi q l e -> Quant qi q l <$> go e
      Lcl l       -> return (Lcl l)
