module HBMC.Merge where

import HBMC.Surgery
import Tip.Core

-- | Assumes commuteMatch has happened, only wades through initial lets
findPoints :: Expr a -> AOSurgery (Global a,[Expr a]) (Expr a) (Expr a,Expr a)
findPoints e0 =
  case e0 of
    Let x e1 e2 -> mapRes (\ (e2',e2_bot) -> (Let x e1 e2,Let x e1 e2_bot)) (findPoints e2)
    _           -> matchPoints e0

-- todo: make this some proper bottom
bot :: Expr a
bot = Builtin At :@: []

-- | Performs surgery on the match points.
--   Two expressions are returned, the first is the actual new expression,
--   whereas the second is merely the skeleton
matchPoints :: Expr a -> AOSurgery (Global a,[Expr a]) (Expr a) (Expr a,Expr a)
matchPoints e0 =
  case e0 of
    hd :@: es ->
      orAO $
        [ mapRes (\ (e',e_bot) -> (hd :@: (l ++ [e'] ++ r),e_bot))
                 (matchPoints e)
        | (l,e,r) <- cursor es
        ] ++
        (case hd of
          Gbl g -> [Surgery (Unit (g,es)) (\(UnitA e) -> (e,e))]
          _     -> [])

    Lcl{} -> retAO (e0,bot)

    Let x e1 e2 -> mapRes (\ (e1',e1_bot) -> (Let x e1' e2,e1_bot)) (matchPoints e1)
                   -- incomplete for now. can let lift+memoise to simplify

    Match e brs ->
      orAO
        [ mapRes (\ (e',e_bot) -> (Match e' brs,e_bot)) (matchPoints e)
        , mapRes (\ rhss -> let (brs',brs_bot) = unzip [ (Case lhs rhs,Case lhs rhs_bot)
                                                       | (Case lhs _,(rhs,rhs_bot)) <- brs `zip` rhss
                                                       ]
                            in  (Match e brs',Match e brs_bot))
                 (andAO [ orAO [matchPoints rhs,retAO (rhs,bot)]
                        | Case _ rhs <- brs
                        ])
        ]

    Lam{}   -> error "matchPoints: Lambda"
    Quant{} -> error "matchPoints: Quant"

cursor :: [a] -> [([a],a,[a])]
cursor xs = [ let (l,x:r) = splitAt i xs in (l,x,r) | i <- [0..length xs-1] ]

