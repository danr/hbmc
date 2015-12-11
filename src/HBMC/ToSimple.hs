{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns, FlexibleContexts #-}
module HBMC.ToSimple where

import Tip.Pretty
import Tip.Pretty.SMT ()
import Control.Applicative( (<$>) )

import Tip.Fresh

import HBMC.Identifiers

import Tip.Core

import Tip.Utils

import Control.Monad.Writer

import Data.Graph

import Data.Monoid

-- E[let x = a in b] ~> let x = a in E[b]
-- but does not pull above Match scopes
widenLetScope :: Expr Var -> Expr Var
widenLetScope e0 =
  let (e0',lets) = runWriter (go e0)
  in  makeLets lets e0'
  where
  go (Match s brs) =
    do s' <- go s;
       return (Match s' brs)

  go (Let x e1 e2) =
    do e1' <- go e1
       tell [(x,e1')]
       go e2

  go (hd :@: es) = (hd :@:) <$> mapM go es

  go (Lcl l) = return (Lcl l)

  go e = error $ "widenLetScope: " ++ ppRender e

-- e ::= let x = f s1 .. sn in e
--    |  let x = c in e
--    |  c
--    |  s
--
-- c ::= case s of K1 -> e1
--                 ...
--                 Kn -> en
--
-- s ::= proj s | K s1 .. sn | x
--
-- + proj (K .. x ..) = x


toExpr :: Expr Var -> Fresh (Expr Var)
toExpr e = inlineOneMatch <$> toExprSimpleEnd e

toExprSimpleEnd :: Expr Var -> Fresh (Expr Var)
toExprSimpleEnd e0 =
  do r <- (`Local` exprType e0) <$> fresh
     let (lets,s) = collectLets (widenLetScope e0)
     (lets',Dual su) <- execWriterT $ sequence_ [ trLet x e | (x,e) <- lets ++ [(r,s)] ]
     -- let lets'' = map fst (concat (orderLets lets'))
     reorderLets <$> substMany su (makeLets lets' (Lcl r))

inlineOneMatch :: Expr Var -> Expr Var
inlineOneMatch e0 =
  case collectLets e0 of
    (lets,Lcl x)
      | (l,m,r):_ <- [ (l,m,r) | (l,(y,m@Match{}),r) <- cursor lets, x == y ]
      , and [ x /= y | (_,e) <- l ++ r, y <- locals e ]
      -> makeLets (l++r) m
    _ -> e0
  where

type Lets a = [(Local a,Expr a)]

type Subst a = Dual [(Local a,Expr a)]

trLet :: Local Var -> Expr Var -> WriterT (Lets Var,Subst Var) Fresh ()
trLet x e0 =
  case e0 of
    Lcl{} -> tell_su e0

    hd@(Gbl (Global f _ _)) :@: args ->
      do xn <- sequence [ do xi <- (`Local` exprType ei) <$> lift (refresh (lcl_name x))
                             trLet xi ei
                             return (Lcl xi)
                        | ei <- args ]
         case () of
           () | isCon f            -> tell_su (hd :@: xn)
              | Just{} <- unproj f -> tell_su (hd :@: xn)
              | otherwise          -> tell_let (hd :@: xn)

    Match e brs ->
      do s <- (`Local` exprType e) <$> lift fresh
         trLet s e
         m <- Match (Lcl s) <$> sequence [ Case pat <$> lift (toExpr rhs)
                                         | Case pat rhs <- brs ]
         tell_let m

    _ -> error $ "trLet: " ++ ppRender e0
  where
  tell_let e = tell ([(x,e)],mempty)
  tell_su  e = tell (mempty,Dual [(x,e)])

orderLets :: forall a . Ord a => Lets a -> [[((Local a,Expr a),[Local a])]]
orderLets lets =
  [ [ ((x,e),lcls)
    | (e,x,lcls) <- comp
    ]
  | comp <- map (flattenSCC) (stronglyConnCompR gr)
  ]
  where
  gr :: [(Expr a,Local a,[Local a])]
  gr = [ (e,x,locals e) | (x,e) <- lets ]

reorderLets :: forall a . Ord a => Expr a -> Expr a
reorderLets e0 =
  let (lets,e) = collectLets e0
  in  makeLets (map fst (concat (orderLets lets))) e

