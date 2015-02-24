{-# LANGUAGE ScopedTypeVariables #-}
module TipData where

import qualified Tip.Types as T
import Tip.Fresh
import Data.List

import TipTarget
import TipMonadic (trType)
import Tip (Datatype(..),Constructor(..))
import Control.Applicative

type DataInfo a = [(a,(a,[Int]))]

dataInfo :: forall a . Eq a => Datatype a -> (DataInfo a,[Type a])
dataInfo (Datatype tc _tvs cons) = (indexes,types)
  where
    types :: [Type a]
    types = merge [ map trType args | Constructor _ args <- cons ]

    indexes =
        [ (c,(tc,index (map trType args) (types `zip` [0..])))
        | Constructor c args <- cons
        ]

    index :: [Type a] -> [(Type a,Int)] -> [Int]
    index []     _  = []
    index (a:as) ts = i : index as (l ++ r)
      where
        (l,(_,i):r) = break ((a ==) . fst) ts

-- | Merging
merge :: Eq a => [[a]] -> [a]
merge []       = []
merge (xs:xss) = help xs (merge xss)
  where
    help :: Eq a => [a] -> [a] -> [a]
    help xs (y:ys) = y:help (delete y xs) ys
    help xs []     = xs

trDatatype :: forall a . Interface a => Datatype a -> Fresh [Decl a]
trDatatype dt@(Datatype tc tvs cons) =
  do constructors <- mapM make_con cons
     case_data <- make_case_data
     make_data <- make_make_data
     equal <- make_equal
     value <- make_value
     return ([wrapper,labels] ++ constructors ++
             [case_data,make_data] ++
             [constructive,equal,repr,value])
 where
  (indexes,types) = dataInfo dt

  strict = and [ null args | Constructor _ args <- cons ]

  a ! b | strict    = b
        | otherwise = a

  me = TyCon (wrapData tc) (map TyVar tvs)

  maybe_tup = TyTup [ TyCon (prelude "Maybe") [modTyCon wrapData t] | t <- types ]

  -- (Thunk (Data N (Maybe Nat)))
  thunk :: Type a
  thunk = thunk_apply (TyCon (api "Data") [TyCon (conLabel tc) [],maybe_tup])
   where
    thunk_apply t | strict    = t
                  | otherwise = TyCon (api "Thunk") [t]

  -- newtype Nat = Nat (Thunk (Data N (Maybe Nat)))
  --  deriving ( Constructive, Equal, Eq )
  wrapper :: Decl a
  wrapper = DataDecl (wrapData tc) tvs
    [(wrapData tc,[thunk])]
    [api "Constructive",api "Equal",prelude "Eq",prelude "Ord"]

  -- caseNat (Nat t) h = ifForce t h
  make_case_data :: Fresh (Decl a)
  make_case_data =
    do t <- fresh
       h <- fresh
       return $
         FunDecl (caseData tc)
           [([ConPat (wrapData tc) [VarPat t],VarPat h]
            ,Apply (api ("ifForce" ! "withoutForce")) [var t,var h])]


  -- makeNat (Nat n) h = doForce t h
  make_make_data :: Fresh (Decl a)
  make_make_data =
    do t <- fresh
       h <- fresh
       return $
         FunDecl (makeData tc)
           [([ConPat (wrapData tc) [VarPat t],VarPat h]
            ,Apply (api ("doForce" ! "withoutForce")) [var t,var h])]



  -- data N = Zero | Succ
  --  deriving ( Eq, Ord, Show )
  labels :: Decl a
  labels = DataDecl (conLabel tc) []
    [ (conLabel c,[]) | Constructor c _ <- cons ]
    (map prelude ["Eq","Ord","Show"])

  -- instance ConstructiveData L where
  --   constrs = [Nil, Cons]
  constructive :: Decl a
  constructive = InstDecl []
    (TyCon (api "ConstructiveData") [TyCon (conLabel tc) []])
    [funDecl (api "constrs") []
      (List [var (conLabel c) | Constructor c _ <- cons ])]

  -- instance Equal a => EqualData R (Maybe a, (Maybe (RE a), (Maybe (RE a), ()))) where
  --   equalData h =
  --     [ ([RAtom],                 \(Just x,_)         (Just y,_)         -> h x y)
  --     , ([RPlus,RAnd,RSeq,RStar], \(_,(Just p,_))     (_,(Just q,_))     -> h p q)
  --     , ([RPlus,RAnd,RSeq],       \(_,(_,(Just p,_))) (_,(_,(Just q,_))) -> h p q)
  --     ]
  make_equal :: Fresh (Decl a)
  make_equal =
    do h <- fresh
       lines <- sequence
         [ do l <- fresh
              r <- fresh
              let lbls = [var (conLabel c) | (c,(_,ixs)) <- indexes, i `elem` ixs]
              let pat b = TupPat $
                    replicate (i) WildPat ++
                    [ConPat (prelude "Just") [VarPat b]] ++
                    replicate (length types - i - 1) WildPat
              return (LinearTup [List lbls,Lam [pat l,pat r] (Apply h [var l,var r])])
         | (_,i) <- types `zip` [0..]
         ]
       return $
         InstDecl
           [TyCon (api "Equal") [TyVar tv] | tv <- tvs]
           (TyCon (api "EqualData") [TyCon (conLabel tc) [],maybe_tup])
           [funDecl (api "equalData") [h] (List lines)]

  -- data Nat_Repr = Zero_Repr | Succ_Repr Nat_Repr | Nat_Thunk
  repr :: Decl a
  repr = DataDecl (conRepr tc) tvs
    ( [ (conRepr c,map (modTyCon conRepr . trType) args)
      | Constructor c args <- cons
      ] ++
      [ (thunkRepr tc,[]) ])
    [prelude "Show"]

  con_prenex :: a -> Fresh ([a],[Maybe a])
  con_prenex c =
    do xn <- sequence [ fresh | _ <- types ]
       let Just (_,ixs) = lookup c indexes
       return (xn,[ fmap (xn !!) (elemIndex p ixs)
                  | (_,p) <- zip types [0..] ])

  -- zer   = Nat (con Zero (Nothing, ()))
  -- suc n = Nat (con Succ (Just n, ()))
  make_con :: Constructor a -> Fresh (Decl a)
  make_con (Constructor c _) =
    do (xn,prenex) <- con_prenex c
       let tuple =
             [ case mx of
                 Just x  -> Apply (prelude "Just") [var x]
                 Nothing -> var (prelude "Nothing")
             | mx <- prenex
             ]
       return $
         funDecl (mkCon c) [ x | Just x <- prenex ]
           (Apply (wrapData tc)
             [Apply (api ("con" ! "conStrict"))
               [var (conLabel c), Tup tuple ]])


  -- f Succ (Just n, ()) = do n' <- get n; return (Succ_Repr n')
  make_get_row :: Constructor a -> Fresh ([Pat a],Expr a)
  make_get_row (Constructor c _) =
    do (xn,prenex) <- con_prenex c
       let tuple =
             [ case mx of
                 Just x  -> ConPat (prelude "Just") [VarPat x]
                 Nothing -> WildPat
             | (_,mx) <- xn `zip` prenex
             ]
       xn' <- mapM (const fresh) xn
       let (args,gets) = unzip
             [ (x',Bind x' (Apply (api "get") [var x]))
             | (x',Just x) <- xn' `zip` prenex
             ]
       return
         ([ConPat (conLabel c) [],TupPat tuple],
          mkDo gets
            (Apply (prelude "return")
              [Apply (conRepr c) (map var args)])
         )

  -- instance Value Nat where
  --   type Type Nat = Nat_Repr
  --
  --   dflt _ = Nat_Thunk
  --
  --   get (Nat t) = getData f Nat_Thunk t
  --    where f = ...
  make_value :: Fresh (Decl a)
  make_value =
    do f <- fresh
       t <- fresh
       f_def <- FunDecl f <$> mapM make_get_row cons
       return $
         InstDecl
           [TyCon (api "Value") [TyVar tv] | tv <- tvs]
           (TyCon (api "Value") [me])
           [AssociatedType
             (TyCon (api "Type") [me])
             (TyCon (conRepr tc) [TyCon (api "Type") [TyVar tv] | tv <- tvs])
           ,FunDecl (api "dflt") [([WildPat],var (thunkRepr tc))]
           ,FunDecl (api "get")
             [([ConPat (wrapData tc) [VarPat t]]
              ,Apply (api ("getData" ! "getStrictData")) [var f,var (thunkRepr tc),var t]
              )]
            `Where` [f_def]
           ]
