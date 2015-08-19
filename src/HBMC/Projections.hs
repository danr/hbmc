{-# LANGUAGE RecordWildCards #-}
module HBMC.Projections where

import Text.Show.Pretty (ppShow)

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

projExpr :: Int -> Expr Var -> Expr Var
projExpr i e = Gbl (Global (proj i) (PolyType [] [] (exprType e)) []) :@: [e]

projectExpr :: DataInfo Var -> Expr Var -> Fresh (Expr Var)
projectExpr di = go
 where
  go e0 =
    case e0 of
      Match e alts ->
        letExpr e $ \ lx ->
        do fmap (Match (Lcl lx))
             (sequence
               [ case pat of
                   Default -> Case Default <$> go rhs
                   ConPat k vars
                     | Just (tc,ixs) <- lookup (gbl_name k) di
                     -> do rhs' <-
                             substMany
                               [ (v,projExpr i (Lcl lx))
                               | (v,i) <- vars `zip` ixs
                               ]
                               rhs
                           Case (ConPat k []) <$> go rhs'
                   _ -> error $ "projectPatterns: " ++ ppShow di ++ "\n" ++ ppRender e0
               | Case pat rhs <- alts
               ])
      hd :@: args -> (hd :@:) <$> mapM go args
      Lam args e  -> Lam args <$> go e
      Let l e1 e2 -> Let l <$> go e1 <*> go e2
      Quant qi q l e -> Quant qi q l <$> go e
      Lcl l       -> return (Lcl l)
