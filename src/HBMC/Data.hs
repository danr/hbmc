{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module HBMC.Data where

import qualified Tip.Types as T
import Tip.Fresh
import Data.List

import Tip.Haskell.Repr as H
import Tip.Utils (recursive)
import Tip.Core  (defines,uses)
import Tip.Pretty

import HBMC.Identifiers
import HBMC.Haskell
import HBMC.Lib hiding (Type,caseData)

import Tip.Core (Datatype(..),Constructor(..))
import Control.Applicative

type DataInfo a = [(a,(a,[Int]))]

dataDescs :: forall a . (Show a,PrettyVar a,Ord a) => [Datatype a] -> a -> LiveDesc a
dataDescs dts = lkup_desc
  where
  rec_dts = recursiveDatatypes dts
  lkup_desc x = case lookup x tbl of Just desc -> desc
                                     Nothing   -> error $ "Data type not found:" ++ varStr x
  tbl =
    [ (tc,
       maybe_thunk $ DataDesc (varStr tc) [ c | Constructor c _ _ <- cons ]
       [ case ty of
           TyCon tc [] ->
             ( [ c | (c,(_,ixs)) <- indexes, i `elem` ixs ]
             , lkup_desc tc)
       | (i,ty) <- [0..] `zip` types ])
    | dt@(Datatype tc [] cons) <- dts
    , let (indexes,types) = dataInfo dt
    , let maybe_thunk | tc `elem` rec_dts = ThunkDesc
                      | otherwise         = id
    ]

recursiveDatatypes :: Ord a => [Datatype a] -> [a]
recursiveDatatypes = recursive defines uses

trType :: T.Type a -> H.Type a
trType t0 =
  case t0 of
    T.TyCon t ts -> H.TyCon t (map trType ts)
    T.TyVar x    -> H.TyVar x
    _            -> error "trType: Cannot translate type\n(using HOFs, classes or Ints?)"

dataInfo :: forall a . Eq a => Datatype a -> (DataInfo a,[Type a])
dataInfo (Datatype tc _tvs cons) = (indexes,types)
  where
    types :: [Type a]
    types = merge [ map (trType . snd) args | Constructor _ _ args <- cons ]

    indexes =
        [ (c,(tc,index (map (trType . snd) args) (types `zip` [0..])))
        | Constructor c _ args <- cons
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

trDatatype :: forall a . (a ~ Var) => [a] -> Bool -> Datatype a -> Fresh [Decl a]
trDatatype rec_dts lazy dt@(Datatype tc tvs cons) =
  do constructors <- mapM make_con cons
     case_data <- make_case_data
     equal <- make_equal
     value <- make_value
     view_data <- make_view_data
     return ([wrapper,labels] ++ constructors ++
             [case_data] ++
             [constructive,equal,repr,value] ++
             [view_tycon,view_data])
 where
  (indexes,types) = dataInfo dt

  strict = not lazy && tc `notElem` rec_dts
        -- and [ null args | Constructor _ _ args <- cons ]

  a ! b | strict    = b
        | otherwise = a

  me = TyCon (wrapData tc) (map TyVar tvs)

  maybe_tup = nestedTyTup [ TyCon (prelude "Maybe") [modTyCon wrapData t] | t <- types ]

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


  -- data N = Zero | Succ
  --  deriving ( Eq, Ord, Show )
  labels :: Decl a
  labels = DataDecl (conLabel tc) []
    [ (conLabel c,[]) | Constructor c _ _ <- cons ]
    (map prelude ["Eq","Ord","Show"])

  -- instance ConstructiveData L where
  --   constrs = [Nil, Cons]
  constructive :: Decl a
  constructive = InstDecl []
    (TyCon (api "ConstructiveData") [TyCon (conLabel tc) []])
    [funDecl (api "constrs") []
      (List [var (conLabel c) | Constructor c _ _ <- cons ])]

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
              let pat b = nestedTupPat $
                    replicate (i) WildPat ++
                    [ConPat (prelude "Just") [VarPat b]] ++
                    replicate (length types - i - 1) WildPat
              return (Tup [List lbls,Lam [pat l,pat r] (Apply h [var l,var r])])
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
    ( [ (conRepr c,map (modTyCon conRepr . trType . snd) args)
      | Constructor c _ args <- cons
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
  make_con (Constructor c _ _) =
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
               [var (conLabel c), nestedTup tuple ]])


  -- f Succ (Just n, ()) = do n' <- get n; return (Succ_Repr n')
  make_get_row :: Constructor a -> Fresh ([Pat a],Expr a)
  make_get_row (Constructor c _ _) =
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
         ([ConPat (conLabel c) [],nestedTupPat tuple],
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
           [TypeDef
             (TyCon (api "Type") [me])
             (TyCon (conRepr tc) [TyCon (api "Type") [TyVar tv] | tv <- tvs])
           ,FunDecl (api "dflt") [([WildPat],var (thunkRepr tc))]
           ,FunDecl (api "get")
             [([ConPat (wrapData tc) [VarPat t]]
              ,Apply (api ("getData" ! "getStrictData")) [var f,var (thunkRepr tc),var t]
              )]
            `Where` [f_def]
           ]

  -- instance IncrView a => IncrView (D_List a) where
  --   incrView (D_List x) = incrView x
  make_view_data :: Fresh (Decl a)
  make_view_data =
    do t <- fresh
       return $
         InstDecl
           [TyCon (api "IncrView") [TyVar tv] | tv <- tvs]
           (TyCon (api "IncrView") [me])
           [FunDecl (api "incrView")
             [([ConPat (wrapData tc) [VarPat t]]
              ,Apply (api ("incrView")) [var t]
              )]]

  -- instance IncrView L where
  --   incrView _ = return "Nat"
  view_tycon :: Decl a
  view_tycon = InstDecl []
    (TyCon (api "IncrView") [TyCon (conLabel tc) []])
    [FunDecl (api "incrView")
      [([WildPat],returnExpr (String (conRepr tc)))]]


