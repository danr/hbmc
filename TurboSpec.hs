{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable #-}
module TurboSpec where

import MiniSat
import qualified Nat as N
import qualified Data.List as L
import Data.Maybe

import qualified Data.Foldable as F

import Symbolic (Bit(..),H,withSolverH,get,nt,Lift(..),Value(..))

newtype Name = Name String
  deriving (Eq,Ord)

instance Show Name where
  show (Name s) = s

makeVars :: Monad m => [name] -> m a -> m [(name,a)]
xs `makeVars` m = sequence [ do a <- m; return (x,a) | x <- xs ]

pairs (x:y:xs) = (x,y) : pairs (y:xs)
pairs _        = []

tight :: [Lt name] -> [Lt name]
tight ls = [ l | l@Def{} <- ls ]

data Lt name
    = Def name [name] name
    | Eq name name
  deriving (Eq, Ord, Functor)

data Tm name
    = App name [Tm name]
    | Var name
  deriving (Eq, Ord, Functor, F.Foldable)

subst :: (name -> Tm name) -> Tm name -> Tm name
subst k (Var n)    = k n
subst k (App f xs) = App f (map (subst k) xs)

substLit :: (name -> Tm name) -> TmLit name -> TmLit name
substLit k (e1 :=: e2) = subst k e1 :=: subst k e2
substLit k (e1 :/: e2) = subst k e1 :/: subst k e2

data TmLit name
    = Tm name :/: Tm name
    | Tm name :=: Tm name
  deriving (Eq, Ord, F.Foldable)

instance Show name => Show (TmLit name) where
    show (e1 :/: e2) = show e1 ++ " /= " ++ show e2
    show (e1 :=: e2) = show e1 ++ " == " ++ show e2

instance Show name => Show (Tm name) where
    show = go 0
      where
        go _ (Var x)    = show x
        go _ (App f []) = show f
        go i (App f [x,y]) | op (show f) = paren (i >= 1) $ go 1 x ++ show f ++ go 1 y
        go i (App f xs) = paren (i >= 2) $ L.intercalate " " (show f:map (go 2) xs)

        paren True s = "(" ++ s ++ ")"
        paren _    s = s

        op :: String -> Bool
        op = all (`elem` ":!#$%&*+./<=>?@|^-~\\{}[]")

ng :: TmLit name -> TmLit name
ng (e1 :=: e2) = e1 :/: e2
ng (e1 :/: e2) = e1 :=: e2

negative (:/:){} = True
negative _       = False

showTermLits :: (Ord name,Show name) => [TmLit name] -> String
showTermLits = decide . L.sort . simplifyTmLits
  where
    decide [l] = show l
    decide lits | all negative lits = L.intercalate " /\\ " (map (show . ng) lits) ++ " ==> _|_"
    decide lits = go lits

    go (l1@(:/:){} : l2@(:/:){} : xs) = show (ng l1) ++ " /\\ " ++ go (l2 : xs)
    go (l1@(:/:){} : l2@(:=:){} : xs) = show (ng l1) ++ " ==> " ++ go (l2 : xs)
    go (l1@(:=:){} : l2@(:=:){} : xs) = show l1      ++ " \\/ " ++ go (l2 : xs)
    go [l@(:=:){}] = show l
    go _ = error "showTermLits"

toTermLits :: [Lt name] -> [TmLit name]
toTermLits = map toTermLit

toTermLit :: Lt name -> TmLit name
toTermLit (Eq a b)     = Var a :=: Var b
toTermLit (Def f xs y) = App f (map Var xs) :/: Var y

simplifyTmLits :: Eq name => [TmLit name] -> [TmLit name]
simplifyTmLits lits = case substitutable lits of
    Just (x,e,rest) -> simplifyTmLits (map (substLit (\ z -> if z == x then e else Var z)) rest)
    Nothing         -> lits

substitutable :: Eq name => [TmLit name] -> Maybe (name,Tm name,[TmLit name])
substitutable xs = case break p xs of
    (l,(e :/: Var x):r) -> Just (x,e,l++r)
    _                   -> Nothing
  where
    p (e :/: Var x) = x `F.notElem` e
    p _ = False

instance Show name => Show (Lt name) where
  show (Def f xs y) = unwords ([show f] ++ map show xs ++ ["!=", show y])
  show (Eq x y)     = unwords [show x,"=",show y]

free :: Ord name => Lt name -> [name]
free (Def _ xs y) = y:xs
free (Eq x y)     = [x,y]

rename :: Ord name => [(name,name)] -> Lt name -> Lt name
rename sub (Def f xs y) = Def f (map (ren sub) xs) (ren sub y)
rename sub (Eq x y)     = eq (ren sub x) (ren sub y)
 where
  eq x y | x < y     = Eq x y
         | otherwise = Eq y x

ren :: Ord name => [(name,name)] -> name -> name
ren sub x = head ([ y | (x',y) <- sub, x == x' ] ++ [x])

turboString :: [[String]] -> [(Lt String,Bit)] -> Solver -> IO ()
turboString svars slits = turbo (map (map Name) svars) [ (fmap Name lit,b) | (lit,b) <- slits ]

turbo :: (Ord name,Show name)
    => [[name]]        -- variable names, grouped by type
    -> [(Lt name,Bit)] -- definitions, and the bit if it is true or not
    -> Solver          -- the solver used for functions
    -> IO ()
turbo vars lits s =
  do s' <- newSolver
     eliminate s' True -- off

     xs <- sequence [ newLit s' | _ <- lits ]
     let tab = [ (t, q, x) | ((t,q),x) <- lits `zip` xs ]

     putStrLn (show (length lits) ++ " literals created.")

     -- count literals
     nLit <- N.count s' $ concat
         [ case l of
            Def _ args _ -> x:[]--replicate (length args) x
            _ -> [x]
         | ((l,_),x) <- lits `zip` xs
         ]

     -- count variables
     nVar <- do
         let vs = concat vars
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
         N.count s' ws

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
       | vs <- vars
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

           my x = case L.find (x `elem`) vars of
                Just mine -> mine
                Nothing   -> error $ "variable " ++ show x ++ " lost!"

         loop nL =
           do -- putStrLn ("Finding candidate (#vars>=" ++ show nV ++", #lits<=" ++ show nL ++ ") ...")
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
                     [ do b <- getWithSolver s' (Lit x)
                          return (l, q, x, b)
                     | (l, q, x) <- tab
                     ]
              let qs = [ (l,q,x) | (l, q, x, True) <- qbs ]
              -- putStrLn "Testing candidate..."
              b <- solve s [ lit (nt q) | (_,q,_) <- qs ]
              if b then
                do xbs <- sequence
                          [ do b <- getWithSolver s q
                               return (x, b)
                          | (l, q, x) <- tab
                          ]
                   -- print [ x | (x, True) <- xbs ]
                   addClause s' [ x | (x, True) <- xbs ]
                   loop nL
               else
                do nv <- N.modelValueNat s' nVar
                   nl <- N.modelValueNat s' nLit
                   -- putStrLn $ " \t" ++ concat (L.intersperse " | " [ show l | (l,_,_) <- qs ])
                   putStrLn $
                        "(" ++ show nv ++ ") "
                     ++ "(" ++ show nl ++ ") "
                     ++ showTermLits (toTermLits [ l | (l,_,_) <- qs ])
                     -- ++ " \t" ++ concat (L.intersperse " | " [ show l | (l,_,_) <- qs ])
                   -- Simple blocks:
                   addClause s' [ neg x | (_,_,x) <- qs ]
                   -- Koen magic:
                   let xs =
                         [ [ neg x
                           | (l, _, x) <- tab
                           , l `elem` tight ls'
                           ]
                         | let ls = [ l | (l,_,_) <- qs ]
                         , sub <- renames (L.nub (concatMap free ls))
                         , let ls' = map (rename sub) ls
                         , all (`elem` [ l | (l,_,_) <- tab ]) ls'
                         ]
                   -- putStrLn $ "Adding " ++ show (length xs) ++ " blocks: " ++ show [ show (length bl) | bl <- xs ]
                   mapM_ (addClause s') xs
                   loop nL

     loop 1
     deleteSolver s
     deleteSolver s'

getWithSolver :: Value a => Solver -> a -> IO (Type a)
getWithSolver s x = do
    mv <- withSolverH s (get x)
    case mv of
        The v -> return v
        UNR   -> error "getWithSolver couldn't get value from model through the H monad - !?"


--------------------------------------------------------------------------------


