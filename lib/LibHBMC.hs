{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, MultiParamTypeClasses, FlexibleInstances, RankNTypes #-}
{-# LANGUAGE FunctionalDependencies, FlexibleContexts #-}
module LibHBMC where

import Control.Applicative
import Control.Monad
import Data.IORef
import Data.List
import qualified Data.Map as Mp
import Data.Unique
import qualified MiniSat as M
import MiniSat ( Solver, Lit )
import System.IO.Unsafe

--------------------------------------------------------------------------------

data Env =
  Env
  { sat   :: Solver
  , here  :: Bit
  , waits :: IORef [(Bit,Unique,H ())]
  }

newtype H a = H (Env -> IO a)

instance Applicative H where
  pure  = return
  (<*>) = ap

instance Functor H where
  fmap = liftM

instance Monad H where
  return x  = H (\_   -> return x)
  H m >>= k = H (\env -> do x <- m env
                            let H m' = k x
                            m' env)

--------------------------------------------------------------------------------

run :: H a -> IO a
run (H m) =
  M.withNewSolver $ \s ->
    do ref <- newIORef []
       m (Env s tt ref)

trySolve :: H (Maybe Bool)
trySolve = H (\env ->
  do ws <- reverse `fmap` readIORef (waits env)
     putStrLn ("== Try solve with " ++ show (length ws) ++ " waits ==")
     putStrLn "Solve..."
     b <- solveBit (sat env) (here env : reverse [ nt p | (p,_,_) <- ws ])
     if b then
       do putStrLn "Counterexample!"
          return (Just True)
      else
        let mini =
              do qs' <- M.conflict (sat env)
                 let qs = [ Lit q | q <- qs' ] ++ [ p | (p,_,_) <- ws, p == tt ]
                 if null qs then
                   do putStrLn "Contradiction!"
                      return (Just False)
                  else
                   let p:_ = [ p | (p,_,_) <- ws, p `elem` qs ] in
                     do putStrLn ("Conflict: " ++ show (length qs))
                        b <- solveBit (sat env) (here env : [ nt q | q <- qs, q /= p ])
                        if b then
                          let (p,unq,H h):_ = [ t | t@(p,_,_) <- ws, p `elem` qs ] in
                            do let ws' = [ t | t@(_,unq',_) <- reverse ws, unq /= unq' ]
                               putStrLn ( "Points: " ++ show (length ws')
                                        )
                               writeIORef (waits env) ws'
                               putStrLn "Expanding..."
                               h env{ here = p }
                               return Nothing
                        else
                         do mini
         in mini

{-
       do putStrLn "Finding a contradiction..."
          b <- solveBit (sat env) [here env]
          if not b then
            do return (Just False)
           else
            let find [] =
                  do return (error "shouldn't happen")

                find ((p,unq,H h):ws) =
                  do b <- solveBit (sat env) [p]
                     if b then
                       do writeIORef (waits env) [ t | t@(_,unq',_) <- reverse ws, unq /= unq' ]
                          putStrLn "!"
                          putStrLn "Expanding..."
                          h env{ here = p }
                          return Nothing
                      else
                       do putStr "X"
                          find ws

             in do writeIORef (waits env) []
                   putStrLn "Finding a point to expand..."
                   find (reverse ws)
-}
  )

solve' :: H () -> H Bool
solve' h =
  do h
     mb <- trySolve
     case mb of
       Nothing -> solve' h
       Just b  -> return b

solve :: H Bool
solve = solve' (return ())

solveAndSee :: (Value a,Show (Type a)) => a -> H ()
solveAndSee see =
  do b <- solve
     if b then
       do get see >>= (io . print)
     else
       do io (putStrLn "No value found.")

io :: IO a -> H a
io m = H (\_ -> m)

withSolver :: (Solver -> IO a) -> H a
withSolver h = H (\env -> h (sat env))

context :: H Bit
context = H (\env -> return (here env))

withExtraContext :: Bit -> H () -> H ()
withExtraContext c _ | c == ff = return ()
withExtraContext c h =
  do x <- new
     addClauseHere [nt c, x]
     c0 <- context
     inContext x (do addClauseHere [c0]; addClauseHere [c]; h)

inContext :: Bit -> H () -> H ()
inContext c _ | c == ff = return ()
inContext c (H m) = H (\env -> m env{ here = c })

later :: Unique -> H () -> H ()
later unq h = H (\env ->
  do ws <- readIORef (waits env)
     writeIORef (waits env) ((here env, unq, h):ws)
  )

check :: H () -> H ()
check h = undefined

must :: Bit -> H () -> H ()
must c h =
  do addClauseHere [c]
     if c == ff then return () else h

addClauseHere :: [Bit] -> H ()
addClauseHere xs =
  do c <- context
     [c] ==> xs

impossible :: H ()
impossible = addClauseHere []

noop :: a -> H ()
noop _ = return ()

when :: Bit -> H () -> H ()
when c h = whens [c] h


-- happens when all of them are false, to deal with default patterns:
--
--   case c
--     K1 -> ..
--     K2 -> ..
--     _  -> e
--
-- becomes:
--
--   unless [c =? K1, c =? K2] $ [[ e ]]
unless :: [Bit] -> H () -> H ()
unless cs h
  | null cs'  = h
  | otherwise =
      do c0 <- context
         c1 <- new
         -- [a1,a2, .. ,aN] = cs'
         -- ~a1 & ~a2 ... & ~aN => c1
         -- a1 | a2 | .. | aN | c1
         addClauseHere (c1:cs)
         inContext c1 $
           do addClauseHere [c0]
              -- in this context, all of a1...aN are false
              sequence_ [ addClauseHere [nt c] | c <- cs' ]
              h
 where
  cs' = filter (/=ff) cs

-- happens when one of them is true
whens :: [Bit] -> H () -> H ()
whens cs h
  | null cs'  = return ()
  | otherwise =
    do c0 <- context
       c1 <- new
       sequence_ [ addClauseHere [nt c, c1] | c <- cs' ]
                               -- c => c1
       inContext c1 $
         do addClauseHere [c0]
            addClauseHere cs'
            h
 where
  cs' = filter (/=ff) cs

choice :: [H ()] -> H ()
choice [h] = h
choice hs =
  do xs <- sequence [ newBit | h <- hs ]
     addClauseHere xs
     a <- context
     sequence_ [ do inContext x (do addClauseHere [a]; h) | (x,h) <- xs `zip` hs ]

ifThenElse :: Bit -> (H (), H ()) -> H ()
ifThenElse b (yes,no) =
  choice [ do addClauseHere [b]; yes, do addClauseHere [nt b]; no ]

--[ call ]----------------------------------------------------------------------

data Call a b =
  Call
  { doit   :: Bit
  , invoke :: a -> (b -> H ()) -> H ()
  }

newCall :: (Constructive a, Constructive b, Equal a, Equal b)
        => (a -> b -> H ()) -> H (Call a b)
newCall h =
  do b <- new
     x <- new
     y <- new
     c <- context
     inContext b $
       do addClauseHere [c]
          h x y
     return $
       Call{ doit   = b
           , invoke = \x' k -> do equalHere x' x
                                  k y
           }

call :: Call a b -> a -> (b -> H ()) -> H ()
call cl x k =
  do addClauseHere [doit cl]
     invoke cl x k

nocall :: Call a b -> H ()
nocall cl =
  do addClauseHere [nt (doit cl)]

--[ memo ]----------------------------------------------------------------------

{-# NOINLINE memo #-}
memo :: (Eq a, Equal b, Constructive b) => String -> (a -> b -> H ()) -> (a -> H b)
memo tag h =
  unsafePerformIO $
    do putStrLn ("Creating table for " ++ tag ++ "...")
       ref <- newIORef []
       return $
         \x -> do xys <- io $ readIORef ref
                  -- io $ putStrLn ("Table size for " ++ tag ++ ": " ++ show (length xys))
                  (c,y) <- case [ (c,y) | (c,x',y) <- xys, x' == x ] of
                             [] ->
                               do y <- new
                                  c <- new
                                  io $ writeIORef ref ((c,x,y):xys)
                                  inContext c $ h x y
                                  return (c,y)

                             (c,y):_ ->
                               do --io $ putStrLn ("Duplicate call: " ++ tag)
                                  return (c,y)

                  addClauseHere [c]
                  return y

{-# NOINLINE nomemo #-}
nomemo :: (Eq a, Equal b, Constructive b) => String -> (a -> b -> H ()) -> a -> H b
nomemo tag h t = do r <- new
                    h t r
                    return r

--------------------------------------------------------------------------------

class Constructive a where
  newPoint :: Bool -> H a

instance Constructive () where
  newPoint _ = return ()

instance Constructive Bit where
  newPoint _ = newBit

instance (Constructive a, Constructive b) => Constructive (a,b) where
  newPoint inp = liftM2 (,) (newPoint inp) (newPoint inp)

instance Constructive a => Constructive (Maybe a) where
  newPoint inp = liftM Just (newPoint inp)

new, newInput :: Constructive a => H a
new      = newPoint False
newInput = newPoint True

--------------------------------------------------------------------------------

class Equal a where
  equal        :: a -> a -> H Bit
  equalHere    :: a -> a -> H ()
  notEqualHere :: a -> a -> H ()

  equal x y =
    do q <- newBit
       inContext q      $ equalHere    x y
       inContext (nt q) $ notEqualHere x y
       return q

  equalHere x y =
    do q <- equal x y
       addClauseHere [q]

  notEqualHere x y =
    do q <- equal x y
       addClauseHere [nt q]

eqTup,neqTup :: Equal a => (a, (a, ())) -> H ()
eqTup  (x, (y, _)) = equalHere x y
neqTup (x, (y, _)) = notEqualHere x y

equalPred :: Equal a => a -> a -> Bit -> H ()
equalPred x y q =
  do q' <- equal x y
     equalHere q q'

instance Equal () where
  equalHere    _ _ = return ()
  notEqualHere _ _ = addClauseHere []

instance Equal Bit where
  equalHere x y
    | x == y    = return ()
    | x == nt y = addClauseHere []
    | otherwise = do addClauseHere [nt x, y]
                     addClauseHere [nt y, x]

  notEqualHere x y = equalHere x (nt y)

instance (Equal a, Equal b) => Equal (a,b) where
  equalHere (x1,x2) (y1,y2) =
    do equalHere x1 y1
       equalHere x2 y2

  notEqualHere (x1,x2) (y1,y2) =
    choice
    [ notEqualHere x1 y1
    , notEqualHere x2 y2
    ]

--------------------------------------------------------------------------------

class Value a where
  type Type a
  dflt :: a -> Type a
  get  :: a -> H (Type a)

instance Value () where
  type Type () = ()
  dflt _ = ()
  get  _ = return ()

instance Value a => Value [a] where
  type Type [a] = [Type a]
  dflt _ = []
  get xs = sequence [ get x | x <- xs ]

instance (Value a, Value b) => Value (a,b) where
  type Type (a,b) = (Type a, Type b)
  dflt ~(x,y) = (dflt x, dflt y)
  get   (x,y) = liftM2 (,) (get x) (get y)

instance Value Bit where
  type Type Bit = Bool
  dflt _ = False
  get (Bool b) = return b
  get (Lit x)  = do Just b <- withSolver (\s -> M.modelValue s x)
                    return b

--------------------------------------------------------------------------------

data Bit = Lit Lit | Bool Bool
 deriving ( Eq, Ord )

instance Show Bit where
  show (Bool b) = if b then "T" else "F"
  show (Lit v)  = show v

newBit :: H Bit
newBit = withSolver (\s -> Lit `fmap` M.newLit s)

ff, tt :: Bit
ff = Bool False
tt = Bool True

nt :: Bit -> Bit
nt (Bool b) = Bool (not b)
nt (Lit x)  = Lit (M.neg x)

andl, orl :: [Bit] -> H Bit
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

addClause :: [Bit] -> H ()
addClause xs
  | tt `elem` xs = do return ()
  | otherwise    = do --io $ putStrLn (show xs)
                      withSolver (\s -> M.addClause s [ x | Lit x <- xs ])
                      return ()

(==>) :: [Bit] -> [Bit] -> H ()
xs ==> ys = addClause (map nt xs ++ ys)

solveBit :: Solver -> [Bit] -> IO Bool
solveBit s xs | ff `elem` xs =
  -- should really also set the conflict clause... :-(
  do return False

solveBit s xs =
  do M.solve s [ x | Lit x <- xs ]

--------------------------------------------------------------------------------

data Thunk a = This a | Delay Bool Unique (IORef (Either (H ()) a))

instance Eq a => Eq (Thunk a) where
  This x      == This y      = x == y
  Delay _ p _ == Delay _ q _ = p == q
  _           == _           = False

this :: a -> Thunk a
this x = This x

delay :: Bool -> H a -> H (Thunk a)
delay inp (H m) =
  do c <- context
     ref <- io $ newIORef undefined
     io $ writeIORef ref (Left (H (\env -> m (env{ here = c }) >>= (writeIORef ref . Right))))
     unq <- io $ newUnique
     return (Delay inp unq ref)

poke :: Thunk a -> H ()
poke (This _)        = do return ()
poke (Delay _ _ ref) =
  do ema <- io $ readIORef ref
     case ema of
       Left m  -> m
       Right _ -> return ()

peek :: Thunk a -> H (Maybe a)
peek (This x)        = return (Just x)
peek (Delay _ _ ref) =
  do ema <- io $ readIORef ref
     return $ case ema of
       Left _  -> Nothing
       Right a -> Just a

force :: Thunk a -> H a
force th =
  do poke th
     Just x <- peek th
     return x

ifForce :: Thunk a -> (a -> H ()) -> H ()
ifForce (This x)               h = h x
ifForce th@(Delay inp unq ref) h =
  do ema <- io $ readIORef ref
     case ema of
       Left m  -> do c <- context
                     io $ writeIORef ref $ Left $
                       do m
                          Just a <- peek th
                          inContext c (h a)
                     if inp then
                       later unq $ poke th
                      else
                       return ()
       Right a -> h a

instance Constructive a => Constructive (Thunk a) where
  newPoint inp = delay inp (newPoint inp)

instance Equal a => Equal (Thunk a) where
  equalHere t1 t2 = equalThunk t1 t2

  notEqualHere t1 t2 =
    ifForce t1 $ \a ->
      do b <- force t2
         notEqualHere a b

equalThunk :: Equal a => Thunk a -> Thunk a -> H ()
equalThunk x y =
  case (x, y) of
    (Delay _ u _, Delay _ v _)
      | u == v -> return ()
      | otherwise ->
         do equalUnique u v (equalThunk' x y)

    _ -> do equalThunk' x y
 where
  equalThunk' x y =
    ifForce x $ \a ->
      do b <- force y
         equalHere a b

equalUnique :: Unique -> Unique -> H () -> H ()
equalUnique =
  unsafePerformIO $
    do ref <- newIORef Mp.empty
       return $ \u v h ->
         do uvs <- io $ readIORef ref
            q <- case Mp.lookup (u,v) uvs of
                   Nothing ->
                      do q <- new
                         io $ writeIORef ref (Mp.insert (u,v) q uvs)
                         inContext q $ h
                         return q

                   Just q ->
                      do --io $ putStrLn "equalHere duplicate!"
                         return q
            addClauseHere [q]

zipThunk :: (a -> b -> H ()) -> Thunk a -> Thunk b -> H ()
zipThunk f t1 t2 =
  ifForce t1 $ \a ->
    do b <- force t2
       f a b

instance Value a => Value (Thunk a) where
  type Type (Thunk a) = Type a

  dflt x = dflt (unThunk x)
   where
    unThunk :: Thunk a -> a
    unThunk ~(This x) = x

  get (This x)        = get x
  get (Delay _ _ ref) =
    do ema <- io $ readIORef ref
       case ema of
         Left _  -> return (dflt (either undefined id ema))
         Right x -> get x

--[ unwrapping ]------------------------------------------------------------------------------

class Unwrap a b | a -> b, b -> a where
  unwrap :: a -> b

caseData :: Unwrap k (Thunk (Data lbl cons)) => k -> (Val lbl -> cons -> H ()) -> H ()
caseData t h = ifForce (unwrap t) (\ (Con lbl cons) -> h lbl cons)

--------------------------------------------------------------------------------

newtype Val a = Val [(Bit,a)] -- sorted on a
 deriving ( Eq, Ord )

instance Show a => Show (Val a) where
  show (Val xs) = concat (intersperse "|" [ show x | (_,x) <- xs ])

val :: a -> Val a
val x = Val [(tt,x)]

(=?),valEq :: Eq a => Val a -> a -> Bit
Val []         =? x  = ff
Val ((a,y):xs) =? x
  | x == y      = a
  | otherwise   = Val xs =? x
valEq = (=?)

domain :: Val a -> [a]
domain (Val xs) = map snd xs

newVal :: Ord a => [a] -> H (Val a)
newVal xs =
  do as <- lits (length ys)
     return (Val (as `zip` ys))
 where
  ys = map head . group . sort $ xs

  lits 1 =
    do return [tt]

  lits 2 =
    do a <- newBit
       return [a,nt a]

  lits n =
    do as <- sequence [ newBit | i <- [1..n] ]
       addClause as
       atMostOne n as
       return as

  atMostOne n as | n <= 5 =
    do sequence_ [ addClause [nt x, nt y] | (x,y) <- pairs as ]
   where
    pairs (x:xs) = [ (x,y) | y <- xs ] ++ pairs xs
    pairs _      = []

  atMostOne n as =
    do a <- newBit
       atMostOne (k+1) (a : take k as)
       atMostOne (n-k+1) (nt a : drop k as)
   where
    k = n `div` 2

instance Ord a => Equal (Val a) where
  equalHere (Val xs) (Val ys) = eq xs ys
   where
    eq [] ys = sequence_ [ addClauseHere [nt y] | (y,_) <- ys ]
    eq xs [] = sequence_ [ addClauseHere [nt x] | (x,_) <- xs ]
    eq ((x,a):xs) ((y,b):ys) =
      case a `compare` b of
        LT -> do addClauseHere [nt x]
                 eq xs ((y,b):ys)
        EQ -> do addClauseHere [nt x, y]
                 eq xs ys
        GT -> do addClauseHere [nt y]
                 eq ((x,a):xs) ys

  notEqualHere (Val xs) (Val ys) = neq xs ys
   where
    neq [] ys = return ()
    neq xs [] = return ()
    neq ((x,a):xs) ((y,b):ys) =
      case a `compare` b of
        LT -> do neq xs ((y,b):ys)
        EQ -> do addClauseHere [nt x, nt y]
                 neq xs ys
        GT -> do neq ((x,a):xs) ys

instance Value (Val a) where
  type Type (Val a) = a

  dflt _ = error "no default value for Val" -- URK

  get (Val xs) =
    do bs <- sequence [ get x | (x,_) <- xs ]
       return (head [ a | (True,(_,a)) <- bs `zip` xs ])

--------------------------------------------------------------------------------

data Data c a = Con (Val c) a
  deriving ( Eq )

con :: Ord c => c -> a -> Thunk (Data c a)
con c a = this (Con (val c) a)

{-
proj :: Maybe a -> (a -> H ()) -> H ()
proj (Just x) h = h x
proj _        _ = return ()
-}

proj1 :: (Maybe a, z) -> (a -> H ()) -> H ()
proj1 (Just x, _) h = h x
proj1 _           _ = return ()

proj2 :: (x, (Maybe a, z)) -> (a -> H ()) -> H ()
proj2 (_, (Just x, _)) h = h x
proj2 _                _ = return ()

proj3 :: (x, (y, (Maybe a, z))) -> (a -> H ()) -> H ()
proj3 (_, (_, (Just x, _))) h = h x
proj3 _                     _ = return ()

proj4 :: (x1, (x, (y, (Maybe a, z)))) -> (a -> H ()) -> H ()
proj4 (_, (_, (_, (Just x, _)))) h = h x
proj4 _                     _ = return ()

proj5 :: (x2, (x1, (x, (y, (Maybe a, z))))) -> (a -> H ()) -> H ()
proj5 (_, (_, (_, (_, (Just x, _))))) h = h x
proj5 _                     _ = return ()

proj6 :: (x3, (x2, (x1, (x, (y, (Maybe a, z)))))) -> (a -> H ()) -> H ()
proj6 (_, (_, (_, (_, (_, (Just x, _)))))) h = h x
proj6 _                     _ = return ()

proj7 :: (x4, (x3, (x2, (x1, (x, (y, (Maybe a, z))))))) -> (a -> H ()) -> H ()
proj7 (_, (_, (_, (_, (_, (_, (Just x, _))))))) h = h x
proj7 _                     _ = return ()

proj8 :: (x5, (x4, (x3, (x2, (x1, (x, (y, (Maybe a, z)))))))) -> (a -> H ()) -> H ()
proj8 (_, (_, (_, (_, (_, (_, (_, (Just x, _)))))))) h = h x
proj8 _                     _ = return ()

class (Show c, Ord c) => ConstructiveData c where
  constrs :: [c]

instance (ConstructiveData c, Constructive a) => Constructive (Data c a) where
  newPoint inp = do vc <- newVal constrs
                    a  <- newPoint inp
                    return (Con vc a)

class ConstructiveData c => EqualData c a where
  equalData :: (forall x . Equal x => x -> x -> H ()) ->
               [([c], a -> a -> H ())]

instance EqualData c a => Equal (Data c a) where
  equalHere (Con c1 x1) (Con c2 x2) =
    do equalHere c1 c2
       c <- context
       sequence_
         [ do x <- new
              sequence_ [ addClauseHere [nt (c1 =? c), x] | c <- cs ]
              inContext x (do addClauseHere [c]; f x1 x2)
         | (cs, f) <- equalData equalHere
         , any (`elem` allcs) cs
         ]
   where
    allcs = domain c1 `intersect` domain c2

  notEqualHere (Con c1 x1) (Con c2 x2) =
    choice
    [ do notEqualHere c1 c2
    , do equalHere c1 c2
         choice
           [ do addClauseHere [ c1 =? c | c <- cs ]
                f x1 x2
           | (cs, f) <- equalData notEqualHere
           , any (`elem` allcs) cs
           ]
     ]
   where
    allcs = domain c1 `intersect` domain c2

getData :: (c -> a -> H b) -> b -> Thunk (Data c a) -> H b
getData f d t =
  do md <- peek t
     case md of
       Nothing -> return d
       Just (Con c a) ->
         do x <- get c
            f x a

