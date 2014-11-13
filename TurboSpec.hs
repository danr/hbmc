{-# LANGUAGE TypeFamilies #-}
module TurboSpec where

import MiniSat
import qualified Nat as N
import qualified Data.List as L
import Data.Maybe

rev :: Symbolic a => Solver -> List a -> IO (List a)
rev s xs =
  caseList s xs
    (return Nil)
    (\_ x xs ->
      do xs' <- rev s xs
         app s xs' (cons x Nil))

app :: Symbolic a => Solver -> List a -> List a -> IO (List a)
app s xs ys =
  caseList s xs
    (return ys)
    (\_ x xs ->
       do zs <- app s xs ys
          return (cons x zs))

insert :: Solver -> Nat -> List Nat -> IO (List Nat)
insert s x xs =
  caseList s xs
    (return (cons x Nil))
    (\_ y ys ->
      do b <- leq s x y
         vs <- insert s x ys
         iff s b (cons x (cons y ys)) (cons y vs))

sort :: Solver -> List Nat -> IO (List Nat)
sort s xs =
  caseList s xs
    (return Nil)
    (\_ x xs ->
      do ys <- sort s xs
         insert s x ys)

merge :: Solver -> List Nat -> List Nat -> IO (List Nat)
merge s xs1 ys1 =
  caseList s xs1
    (return ys1)
    (\cx x xs ->
      caseList' s [cx] ys1
        (return xs1)
        (\_ y ys ->
          do b <- leq s x y
             as <- iff s b xs xs1
             bs <- iff s b ys1 ys
             ms <- merge s as bs
             iff s b (cons x ms) (cons y ms)
    ))

flatten :: Symbolic a => Solver -> TREE a -> IO (List a)
flatten s t =
  caseTree s t
    (return Nil)
    (\_ p x q ->
      do as <- flatten s p
         bs <- flatten s q
         app s as (cons x bs))

--------------------------------------------------------------------------------

(!) :: Solver -> IO Bit -> IO ()
s ! m = do b <- m; addClauseBit s [b]

vars :: [String] -> IO a -> IO [(String,a)]
xs `vars` m = sequence [ do a <- m; return (x,a) | x <- xs ]

pairs (x:y:xs) = (x,y) : pairs (y:xs)
pairs _        = []

turbo :: IO ()
turbo =
  do s <- newSolver
     eliminate s True -- off

     s' <- newSolver
     eliminate s' True -- off

     putStrLn "*** Creating problem..."

     xas  <- ["X", "Y"] `vars` newNat s 3
     xsas <- ["Xs", "Ys", "Zs", "Vs", "Ws", "Ps", "Qs"] `vars` newLists s 5 (newNat s 3)

     lits <- sequence $
             {-
             [ do bs' <- insert s a as
                  b <- equal s bs bs'
                  return (Def "insert" [x,xs] ys, nt b)
             | (x,a) <- xas
             , (xs,as) <- xsas
             , (ys,bs) <- xsas
             ] ++
             -}
             [ do cs' <- app s as bs
                  b <- equal s cs cs'
                  return (Def "app" [xs,ys] zs, nt b)
             | (xs,as) <- xsas
             , (ys,bs) <- xsas
             , (zs,cs) <- xsas
             ] ++
             {-
             [ do bs' <- sort s as
                  b <- equal s bs bs'
                  return (Def "sort" [xs] ys, nt b)
             | (xs,as) <- xsas
             , (ys,bs) <- xsas
             ] ++
             -}
             [ do b <- equal s as bs
                  return (Eq xs ys, b)
             | (xs,as):_ <- [xsas]
             , _:(ys,bs):_ <- [xsas]
             , xs < ys
             ] ++
             {-
             [ do b <- equal s a b
                  return (Eq x y, b)
             | (x,a):_ <- [xas]
             , _:(y,b):_ <- [xas]
             , x < y
             ] ++
             -}
             []

     xs <- sequence [ newLit s' | _ <- lits ]
     let tab = [ (t, q, x) | ((t,q),x) <- lits `zip` xs ]

     putStrLn (show (length lits) ++ " literals created.")

     -- count literals
     nLit <- N.count s' xs

     -- count variables
     let vs = map fst xas ++ map fst xsas
     ws <- sequence [ newLit s' | v <- vs ]
     sequence_
       [ addClause s' (neg w : [ x | (l, _, x) <- tab, v `elem` free l ])
       | (v,w) <- vs `zip` ws
       ]
     sequence_
       [ addClause s' [w, neg x]
       | (v,w) <- vs `zip` ws
       , (l, _, x) <- tab
       , v `elem` free l
       ]
     nVar <- N.count s' ws

     -- at least one literal
     addClause s' xs

     -- no definition twice
     sequence_
       [ addClause s' [neg l, neg l']
       | (Def f xs y, _, l) <- tab
       , (Def f' xs' y', _, l') <- tab
       , (f,xs) == (f',xs')
       , y < y'
       ]

     -- symmetry: if a bigger variable is used, then a smaller one must be used too
     sequence_
       [ addClause s' (neg x : [ y | (l,_,y) <- tab, v `elem` free l ])
       | vs <- [map fst xas, map fst xsas]
       , (v,w) <- pairs vs
       , (l, _, x) <- tab
       , w `elem` free l
       , v `notElem` free l
       ]

     true <- newLit s
     addClause s [true]

     let lit (Bool b) = if b then true else neg true
         lit (Lit x)  = x

         renames vs = cross [ (v, my v) | v <- vs ]
          where
           cross ((x,xs):ws) = [ (x,y):sub | y <- xs, sub <- cross ws ]
           cross []          = [ [] ]

           my x | x `elem` map fst xas  = map fst xas
                | x `elem` map fst xsas = map fst xsas

         loop nL =
           do --putStrLn ("Finding candidate (#vars>=" ++ show nV ++", #lits<=" ++ show nL ++ ") ...")
              b <- solve s' [nLit N..<= nL] -- nVar
              if b then
                candidate nL
               else
                do b <- solve s' []
                   if b then
                     do loop (nL+1)
                    else
                     do return ()

         candidate nL =
           do qbs <- sequence
                     [ do b <- get s' (Lit x)
                          return (l, q, x, b)
                     | (l, q, x) <- tab
                     ]
              let qs = [ (l,q,x) | (l, q, x, True) <- qbs ]
              --putStrLn "Testing candidate..."
              b <- solve s [ lit (nt q) | (_,q,_) <- qs ]
              if b then
                do xbs <- sequence
                          [ do b <- get s q
                               return (x, b)
                          | (l, q, x) <- tab
                          ]
                   addClause s' [ x | (x, True) <- xbs ]
                   loop nL
               else
                do nv <- N.modelValueNat s' nVar
                   putStrLn ("(" ++ show nv ++ ") " ++ concat (L.intersperse " | " [ show l | (l,_,_) <- qs ]))
                   sequence_
                     [ addClause s' [ neg x
                                    | (l, _, x) <- tab
                                    , l `elem` tight ls'
                                    ]
                     | let ls = [ l | (l,_,_) <- qs ]
                     , sub <- renames (L.nub (concatMap free ls))
                     , let ls' = map (rename sub) ls
                     , all (`elem` [ l | (l,_,_) <- tab ]) ls'
                     ]
                   loop nL

     loop 1
     deleteSolver s
     deleteSolver s'

tight :: [Lt] -> [Lt]
tight ls = [ l | l@(Def _ _ _) <- ls ]

data Lt = Def Name [Name] Name
        | Eq Name Name
       deriving ( Eq, Ord )

instance Show Lt where
  show (Def f xs y) = unwords ([f] ++ xs ++ ["!=", y])
  show (Eq x y)     = unwords [x,"=",y]

free :: Lt -> [Name]
free (Def _ xs y) = y:xs
free (Eq x y)     = [x,y]

rename :: [(Name,Name)] -> Lt -> Lt
rename sub (Def f xs y) = Def f (map (ren sub) xs) (ren sub y)
rename sub (Eq x y)     = eq (ren sub x) (ren sub y)
 where
  eq x y | x < y     = Eq x y
         | otherwise = Eq y x

ren :: [(Name,Name)] -> Name -> Name
ren sub x = head ([ y | (x',y) <- sub, x == x' ] ++ [x])

--------------------------------------------------------------------------------


