module Main where

import MiniSat ( Solver, Lit )
import qualified MiniSat as M
import Data.Set ( Set )
import qualified Data.Set as S
import Data.List ( (\\) )
import qualified Nat as N

--------------------------------------------------------------------------------

newtype M a = M (Solver -> IO (Maybe a))

instance Functor M where
  f `fmap` M m = M (\s -> do mx <- m s
                             return (f `fmap` mx))

instance Monad M where
  return x  = M (\_ -> return (Just x))
  M m >>= k = M (\s -> do mx <- m s
                          case mx of
                            Nothing -> return Nothing
                            Just x  -> let M m' = k x in m' s)
  fail _    = M (\_ -> return Nothing)

run :: M a -> IO (Maybe a)
run (M m) =
  do s <- M.newSolver
     M.eliminate s True
     mx <- m s
     M.deleteSolver s
     return mx

peek :: M a -> M (Maybe a)
peek (M m) = M (\s -> do mx <- m s; return (Just mx))

io :: IO a -> M a
io m = M (\_ -> Just `fmap` m)

withSolver :: (Solver -> IO a) -> M a
withSolver f = M (\s -> Just `fmap` f s)

imp :: Set Bit -> M a
imp xs =
  do --io $ print (S.toList xs)
     addClause [ nt x | x <- S.toList xs ]
     fail "impossible"

--------------------------------------------------------------------------------

data Bit = Lit Lit | Bool Bool
 deriving ( Eq, Ord )

instance Show Bit where
  show (Bool b) = if b then "T" else "F"
  show (Lit v)  = show v

newBit :: M Bit
newBit = withSolver (\s -> Lit `fmap` M.newLit s)

ff, tt :: Bit
ff = Bool False
tt = Bool True

nt :: Bit -> Bit
nt (Bool b) = Bool (not b)
nt (Lit x)  = Lit (M.neg x)

andl, orl :: [Bit] -> M Bit
andl xs
  | ff `elem` xs = return ff
  | otherwise    = withSolver (\s -> andl' s [ x | Lit x <- xs ])
 where
  andl' s []  = do return tt
  andl' s [x] = do return (Lit x)
  andl' s xs  = do y <- M.newLit s
                   M.addClause s (y : map M.neg xs)
                   sequence_ [ M.addClause s [M.neg y, x] | x <- xs ]
                   return (Lit y)

orl xs = nt `fmap` andl (map nt xs)

addClause :: [Bit] -> M ()
addClause xs
  | tt `elem` xs = do return ()
  | otherwise    = do withSolver (\s -> M.addClause s [ x | Lit x <- xs ])
                      return ()

(==>) :: [Bit] -> [Bit] -> M ()
xs ==> ys = addClause (map nt xs ++ ys)

--------------------------------------------------------------------------------

getBool :: Bit -> M (Bit,Bool)
getBool x =
  do Just b <- case x of
                 Lit y  -> withSolver (\s -> M.modelValue s y)
                 Bool b -> return (Just b)
     return (if b then x else nt x,b)

type Index = [Bit]

(=?) :: Index -> Int -> Bit
(x:xs) =? 0 = x
(x:xs) =? i = xs =? (i-1)
_      =? _ = ff

newIndex :: Int -> M Index
newIndex n =
  do xs <- sequence [ newBit | i <- [0..n] ]
     addClause xs
     sequence_ [ addClause [nt x, nt y] | x <- xs, y <- xs, x < y ]
     return xs

getIndex :: Index -> M (Bit,Int)
getIndex (x:xs) =
  do (z,b) <- getBool x
     if b then
       do return (z,0)
      else
       do (y,n) <- getIndex xs
          return (y,n+1)

--------------------------------------------------------------------------------

type Fun = (Bit,Index,Index)
type Var = Index

data Expr
  = Let Bit (Fun,Expr) Expr
  | Case Bit Var Expr Expr
  | Simple Bit Var Bit Expr Expr
 deriving ( Eq, Ord, Show )

type Program = [Expr]

data V = O | V :*: V | Abs Int | Set Bit :=> V
 deriving ( Eq, Ord, Show )

type Env = [V]

data Reason a = Set Bit :==> a
 deriving ( Eq, Ord, Show )

--------------------------------------------------------------------------------

type Name = String

new :: [Name] -> Name
new env = head (vars \\ env)
 where
  vars = ["x","y","z","v","w","p","q","r"] ++ ["x" ++ show i | i <- [1..] ]

type Doc = [String]

text :: String -> Doc
text s = [s]

nest :: Int -> Doc -> Doc
nest d xs = map (replicate d ' ' ++) xs

(#), (##), ($$) :: Doc -> Doc -> Doc
xs # ys = init xs ++ [lxs ++ head ys] ++ nest n (tail ys)
 where
  lxs = last xs
  n   = length lxs

xs ## ys = xs # (text " " # ys)

xs $$ ys = xs ++ ys

par True  d = text "(" # d # text ")"
par False d = d

env ?? i | i < length env = env !! i
         | otherwise      = "?" ++ show i

docExpr :: Bool -> [Name] -> Expr -> M Doc
docExpr atom env (Let on ((prim,p,f),a) e) =
  do (_,b) <- getBool on
     if b then
       do (_,b) <- getBool prim
          (_,j) <- getIndex p
          (_,i) <- getIndex f
          da <- docExpr False env a
          de <- docExpr False (v:env) e
          return (par atom ((text "let" ## text v ## text "=" ## text (fun (b,j,i)) # text "(" # da # text ") in")
                          $$ nest 2 de))
      else
       do docExpr atom ("?":env) e
 where
  v = new env
  
  fun (False,_,i) = "f" ++ show i
  fun (True,0,_)  = "eq"
  fun (True,1,_)  = "leq"

docExpr atom env (Case on v nl cns) =
  do (_,b) <- getBool on
     if b then
       do (_,i) <- getIndex v
          dnl <- docExpr False env nl
          dcns <- docExpr False (x:y:env) cns
          return ( par atom ((text "case" ## text (env??i) ## text "of")
                $$ nest 2 ( (text "O ->" ## dnl)
                         $$ (text x ## text ":*:" ## text y ## text "->" ## dcns)
                          )
                 ))
      else
       do docExpr atom env nl
 where
  x = new env
  y = new (x:env)

docExpr atom env (Simple onVar v onCons e1 e2) =
  do (_,b) <- getBool onVar
     if b then
       do (_,i) <- getIndex v
          return (text (env ?? i))
      else
       do (_,b) <- getBool onCons
          if b then
            do de1 <- docExpr True env e1
               de2 <- docExpr True env e2
               return (par atom (de1 ## text ":*:" ## de2))
           else
            do return (text "O")

docProgram :: Program -> M Doc
docProgram es =
  do des <- sequence [ docExpr False ["a"] e | e <- es ]
     return (foldr1 ($$) [ text ("f" ++ show i ++ "(a) = ") # de | (de,i) <- des `zip` [0..] ])

--------------------------------------------------------------------------------

indx s xs i | i < length xs = xs !! i
            | otherwise     = error ("index " ++ s ++ ": " ++ show i)

eval :: Int -> Program -> Env -> Reason Expr -> M V
eval k prg env (xs :==> e) | k < 0 =
  do imp xs

eval k prg env (xs :==> Let on (f,a) e) =
  do (x,b) <- getBool on
     vb <- if b then
             do va <- eval k prg env ((S.insert x xs) :==> a)
                apply k prg (S.insert x xs :==> f) va
            else
             do return (error "undefined variable")
     eval k prg (vb:env) (xs :==> e)

eval k prg env (xs :==> Case on v e_nl cns) =
  do (x,b) <- getBool on
     if b then
       -- case
       do (y,i) <- getIndex v
          let match zs O          = eval k prg env (zs :==> e_nl)
              match zs (p :*: q)  = eval k prg ((zs :=> p):(zs :=> q):env) (zs :==> cns)
              match zs (ws :=> p) = match (ws `S.union` zs) p
              match zs (Abs _)    = imp zs
          match (S.insert x (S.insert y xs)) (indx "env-case" env i)
      else
       -- no case
       do eval k prg env ((S.insert x xs) :==> e_nl)

eval k prg env (xs :==> Simple onVar v onCons e1 e2) =
  do (x,b) <- getBool onVar
     if b then
       -- variable
       do (y,i) <- getIndex v
          let a = indx "env-var" env i
          return ((S.insert x (S.insert y xs)) :=> a)
      else
       do (y,b) <- getBool onCons
          if b then
            -- cons
            do let ys = S.insert y xs
               a1 <- eval k prg env (ys :==> e1)
               a2 <- eval k prg env (ys :==> e2)
               return (ys :=> (a1 :*: a2))
           else
            -- nil
            do return ((S.insert x (S.insert y xs)) :=> O)

--------------------------------------------------------------------------------

apply :: Int -> Program -> Reason Fun -> V -> M V
apply k prg (xs :==> (prim,p,f)) va =
  do (x,b) <- getBool prim
     if b then
       do (y,i) <- getIndex p
          return (S.insert y (S.insert x xs) :=> peval i va)
      else
       do (y,i) <- getIndex f
          eval (k-1) prg [va] ((S.insert y (S.insert x xs)) :==> (indx "prg" prg i))

numPrims = 1

peval :: Int -> V -> V
peval i a
  | i == 0 = eq a
  | i == 1 = leq a
 where
  eq  a = onPair eq' a
  leq a = lt a ||| eq a
  lt  a = onPair lt' a

  onPair f O                  = O
  onPair f (Abs _)            = O
  onPair f (xs :=> p)         = xs :=> onPair f p
  onPair f ((xs :=> p) :*: q) = xs :=> onPair f (p :*: q)
  onPair f (p :*: (xs :=> q)) = xs :=> onPair f (p :*: q)
  onPair f (p :*: q)          = f p q

  eq' O         O         = O:*:O
  eq' (Abs x)   (Abs y)   | x == y = O:*:O
  eq' (x1:*:x2) (y1:*:y2) = eq (x1:*:y1) &&& eq (x2:*:y2)
  eq' _         _         = O
  
  lt' _         O         = O
  lt' O         _         = O:*:O
  lt' (Abs x)   (Abs y)   = if x < y then O:*:O else O
  lt' (Abs x)   _         = O:*:O
  lt' _         (Abs y)   = O
  lt' (x1:*:x2) (y1:*:y2) = lt (x1:*:y1) ||| (eq (x1:*:y1) &&& lt (x2:*:y2))

fuel (xs :=> p) = (xs `S.union` ys,q) where (ys,q) = fuel p
fuel p          = (S.empty,p)

p &&& q = case (fuel p, fuel q) of
            ((xs, O), _)       -> xs :=> O
            (_,       (ys, O)) -> ys :=> O
            ((xs, _), (ys, _)) -> (xs `S.union` ys) :=> (O:*:O)

p ||| q = case (fuel p, fuel q) of
            ((xs, O:*:O), _)     -> xs :=> (O:*:O)
            (_,     (ys, O:*:O)) -> ys :=> (O:*:O)
            ((xs, _), (ys, _))   -> (xs `S.union` ys) :=> O

nott p = case fuel p of
           (xs, O) -> xs :=> (O:*:O)
           (xs, _) -> xs :=> O

--------------------------------------------------------------------------------

e0 = error "bad expression"

newExpr :: (Int,Int,Int) -> Int -> Int -> M Expr
newExpr (0,0,0) p e =
  do onVar <- newBit
     v <- newIndex e
     return (Simple onVar v ff e0 e0)

newExpr (0,0,dk) p e =
  do onVar <- newBit
     v <- newIndex e
     onCons <- newBit
     addClause [nt onVar, nt onCons]
     a <- newExpr (0,0,dk-1) p e
     b <- newExpr (0,0,dk-1) p e
     return (Simple onVar v onCons a b)

newExpr (0,dl,dk) p e =
  do on <- newBit
     pf <- newBit
     pr <- newIndex (numPrims-1)
     f <- newIndex p
     a <- newExpr (0,0,dk) p e
     e1 <- newExpr (0,dl-1,dk) p (e+1)
     return (Let on ((pf,pr,f),a) e1)

newExpr (dc,dl,dk) p e =
  do on <- newBit
     v <- newIndex (1 `min` e) -- always use a variable that has just been introduced
     nl <- newExpr (0,dl,dk) p e
     cns <- newExpr (dc-1,dl,dk) p (e+2)
     return (Case on v nl cns)

--------------------------------------------------------------------------------

invVar :: [Bit] -> Expr -> M ()
invVar env (Let on (f,a) e) =
  do invVar env a
     invVar (on:env) e

invVar env (Case on v nl cns) =
  do sequence_ [ addClause [nt on, nt (v =? i), e]
               | (e,i) <- env `zip` [0..]
               ]
     env' <- sequence [ do notV <- orl [nt on, nt (v =? i)]
                           andl [e,notV]
                      | (e,i) <- env `zip` [0..]
                      ]
     invVar env' nl
     invVar (on:on:env') cns

invVar env (Simple onVar v onCons e1 e2) =
  do sequence_ [ addClause [nt onVar, nt (v =? i), e]
               | (e,i) <- env `zip` [0..]
               ]
     if onCons /= ff then
       do invVar env e1
          invVar env e2
      else
       do return ()

invCase :: Expr -> M ()
invCase (Let _ (_,a) e) =
  do invCase a
     invCase e

invCase (Case on v nil cns) =
  do invCase nil
     invCase cns
     case cns of
       Case on' v' _ _ ->
         do addClause [nt on', on]
            
       _ -> return ()

invCase (Simple _ _ onCons a b) =
  if onCons == ff then
    do return ()
   else
    do invCase a
       invCase b

invLet :: [Bit] -> Expr -> M [Bit]
invLet act (Let on (_,a) e) =
  do pat1 <- invLet (on:act) a
     pat2 <- invLet act e
     addClause (map nt act ++ [nt on, fstPat pat2])
     case e of
       Let on' _ _ -> addClause [nt on', on]
       _           -> return ()
     orPat pat1 (drop 1 pat2)

invLet act (Case on v nil cns) =
  do pat1 <- invLet act nil
     pat2 <- invLet (on:act) cns
     pat3 <- useVar (on:act) v
     pat12 <- orPat pat1 (drop 2 pat2)
     orPat pat12 pat3

invLet act (Simple onVar v onCons a b) =
  if onCons == ff then
    do useVar (onVar:act) v
   else
    do pat1 <- useVar (onVar:act) v
       pat2 <- invLet (onCons:act) a
       pat3 <- invLet (onCons:act) b
       pat12 <- orPat pat1 pat2
       orPat pat12 pat3

fstPat []    = ff
fstPat (x:_) = x

orPat []     []     = return []
orPat (x:xs) (y:ys) = do z <- orl [x,y]
                         zs <- orPat xs ys
                         return (z:zs)
orPat xs     []     = return xs
orPat []     ys     = return ys

useVar act xs =
  sequence [ andl (x:act) | x <- xs ]

--------------------------------------------------------------------------------

switches :: Expr -> [Bit]
switches (Let on (_,a) e)            = on : switches a ++ switches e
switches (Case on v nl cns)          = on : switches nl ++ switches cns
switches (Simple onVar v onCons a b) = {- onVar : -} onCons : (if onCons == ff then [] else switches a ++ switches b)

--------------------------------------------------------------------------------

class Value a where
  value :: a -> V

instance Value V where
  value x = x

instance Value Bool where
  value False = O
  value True  = O :*: O

instance Value Int where
  value x = Abs x

instance Value Integer where
  value 0 = O
  value n = O :*: value (n-1)

instance Value a => Value [a] where
  value []     = O
  value (x:xs) = value x :*: value xs

instance Value a => Value (Maybe a) where
  value Nothing  = O
  value (Just x) = O :*: value x

instance (Value a, Value b) => Value (a,b) where
  value (x,y) = value x :*: value y

--------------------------------------------------------------------------------

size :: V -> Int
size O         = 1
size (x :*: y) = 1 + size x + size y
size (Abs _)   = 1
size (_ :=> x) = size x

--------------------------------------------------------------------------------

--f (a,b) = a
--inputs = [ (0,0), (0,1), (1,0), (1,1), (2,3), (5::Int,2::Int) ]

--f (a,b) = a++b
--inputs = [ ([],[]), ([1],[]), ([],[1]), ([1,2],[3,4,5]::[Int]) ]

--f (a,b) = a+b
--inputs = [ (0,0), (0,1), (1,0), (1,1), (2,3), (5,2::Integer) ]

--f (a,b) = a*b
--inputs = [ (0,0), (0,1), (1,0), (1,1), (1,3), (4,1), (1,5), (2,2), (2,3), (5,2::Integer), (3,3) ]

--f xs = even (length [ x | x <- xs, x ])
--inputs = take 15 ([] : [ b:ys | ys <- inputs, b <- [False,True] ])

--f (a,b) = a==b
--inputs = [ (0,0), (0,1), (1,0), (1,1), (2,2), (2,3), (3,4), (4,4::Integer), (6,6) ]

--f (a,b) = a<=b
--inputs = [ ([],[]), ([0],[]), ([],[1,2]), ([1,2],[1,2]), ([1,2,3],[2,3]), ([1,2,3::Int],[1,2,3::Int]) ]

--f as = sum as
--inputs = [ [], [0], [1], [3], [1,2], [0,3,2], [1,1,0,2::Integer] ]

{-
f (a,b) = a `elem` b
inputs = [ (1,[])
         , (1,[2]), (1,[1]), (1,[1,2]), (1,[2,1]), (1,[2,3])
         , (1,[1,2,3]), (3,[1,2,3]), (1,[2,3,4])
         , (1,[2,2,1,2]), (1,[3,3,2,1]), (1,[2,3,4,5::Int])
         ]
-}

--f xs = reverse xs
--inputs = [ [], [1], [1,2], [1,2,3,4]::[Int] ]

f (gr,(a,b)) = find [] gr a b
 where
  find seen gr a b
    | a == b        = True
    | a `elem` seen = False
    | otherwise     = or [ find (a:seen) gr a' b | (a0,a') <- gr, a0 == a ]

inputs = [ ([],(1,1::Int))
         , ([],(1,2))
         , ([(1,2),(2,3)],(1,2))
         , ([(1,2),(2,3)],(1,3))
         , ([(1,2),(2,3)],(3,1))
         , ([(1,2),(1,3)],(2,3))
         , ([(1,2),(1,3),(3,1)],(2,3))
         , ([(1,2),(1,3),(3,1)],(1,3))
         , ([(1,2),(1,3),(3,1)],(2,1))
         ]

runTime n = 2*n
numFuns = 2

--------------------------------------------------------------------------------

main =
  do run findProgram
     return ()

findProgram =
  do -- creating program
     es <- sequence [ newExpr (2,2,2) (numFuns-1) 0 | i <- [1..numFuns] ]
     sequence_ [ do invVar [tt] e
                    invCase e
                    invLet [] e
               | e <- es
               ]
     let ons = concatMap switches es
     nn <- withSolver $ \s -> N.count s [ x | Lit x <- ons ]

     -- checking for equality
     let equal xs (ys :=> p)  q           = equal (ys `S.union` xs) p q
         equal xs p           (zs :=> q)  = equal (zs `S.union` xs) p q
         equal xs (p1 :*: p2) (q1 :*: q2) = do equal xs p1 q1
                                               equal xs p2 q2
         equal xs O           O           = return ()
         equal xs (Abs x)     (Abs y) | x == y = return ()
         equal xs _           _           = imp xs

     -- running one test
     let test inp out =
           do res <- eval (runTime (size inp)) es [inp] (S.empty :==> (es!!0))
              equal S.empty res out
         
     -- running many tests
     let tests n [] =
           do return Nothing
         
         tests n (i:is) =
           do mr <- peek (test inp out)
              case mr of
                Just () -> tests (n+1) is
                Nothing -> return (Just (n,i,f i))
          where
           inp = value i
           out = value (f i)
         
     -- looping until a solution is found
     let loop best =
           do b <- withSolver $ \s -> N.solveMinimize s [] nn
              if b then
                do mn <- tests 0 inputs
                   case mn of
                     Nothing ->
                       do io $ putStrLn "=== SOLUTION ==="
                          dp <- docProgram es
                          io $ putStr $ unlines $ dp
                     
                     Just (n,i,j) | n >= best ->
                       do io $ putStrLn ("=== PASSES " ++ show n ++ "/" ++ show (length inputs) ++ " tests, FAILS for " ++ show i ++ "->" ++ show j ++ " ===")
                          dp <- docProgram es
                          io $ putStr $ unlines $ dp
                          loop (n `max` best)
                     
                     _ ->
                       do loop best
              else
               do io $ putStrLn "*** NO SOLUTION ***"

     -- calling loop
     loop 0

