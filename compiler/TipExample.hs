{-# LANGUAGE FlexibleContexts #-}
module TipExample where

import Tip
import Tip.Fresh
import Tip.Pretty

import TipLift

merge :: Call String => Expr String
merge =
  Match (Lcl xs0)
    [ Case (ConPat nil []) (Lcl ys0)
    , Case (ConPat cons [x,xs]) $
       Match (Lcl ys)
         [ Case (ConPat nil []) (Lcl xs0)
         , Case (ConPat cons [y,ys]) $
            Match (Gbl (fun "<") :@: [Lcl x,Lcl y])
              [ Case (LitPat (Bool True))  (Gbl cons :@: [Lcl x, (Gbl merg :@: [Lcl xs,Lcl ys0]) @@ 1])
              , Case (LitPat (Bool False)) (Gbl cons :@: [Lcl y, (Gbl merg :@: [Lcl xs0,Lcl ys]) @@ 1])
              ]
         ]
    ]
 where
  xs0 = lcl "xs0"
  xs  = lcl "xs"
  x   = lcl "x"
  ys0 = lcl "ys0"
  ys  = lcl "ys"
  y   = lcl "y"
  merg = fun "merge"

nil  = con "nil"
cons = con "cons"

con a = Global a NoPolyType [] ConstructorNS

e @@ i = Gbl (fun labelName) :@: [literal (Int i),e]

lcl a = Local a NoType
