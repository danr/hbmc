{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, MultiParamTypeClasses, FlexibleInstances, RankNTypes, FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
module HBMC.Lib where

import Control.Applicative
import Control.Monad hiding (when,unless)
import Data.IORef
import Data.List
import qualified Data.Map as Mp
import Data.Unique
import qualified MiniSat as M
import MiniSat ( Solver, Lit )
import System.IO.Unsafe
import Data.Function (on)

import Debug.Trace

import Text.Show.Pretty (parseValue,valToStr)

import HBMC.Params hiding (getParams)

--------------------------------------------------------------------------------

data Source = Check | Input
  deriving (Eq,Ord)

instance Show Source where
  show Check = "check"
  show Input = "input"

data Env =
  Env
  { sat    :: Solver
  , here   :: Bit
  , waits  :: IORef [(Source,(Bit,Unique,H ()))]
  , params :: Params
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

run :: Params -> H a -> IO a
run p (H m) =
  M.withNewSolver $ \s ->
    do refw <- newIORef []
       m (Env s tt refw p)

{-

new conflict minimization algorithm

call:

  miniConflict xs []

with a list of assumptions xs, of which you already know there was a conflict

miniConflict xs ys =
  do qs <- conflict
     let x:_ = [ x | x <- xs, x `elem` qs ]
         xs' = dropWhile (/= x) xs

     let search [x] ys =
           do return x

         search xs ys =
           do b <- solve (xs1 ++ ys)
              if b then
                search xs0 (xs1 ++ ys)
               else
                miniConflict xs1 ys
          where
           k = length xs `div` 2
           xs0 = take k xs
           xs1 = drop k xs
-}

trySolve :: H (Maybe Bool)
trySolve = H (\env ->
  do let Params{..} = params env
     let verbose | quiet     = const (return ())
                 | otherwise = putStrLn
     ws <- reverse `fmap` readIORef (waits env)
     verbose $ "== Try solve with " ++ show (length ws) ++ " waits =="
     b <- solveBit (sat env) (here env : reverse [ nt p | (_,(p,_,_)) <- ws ])
     if b then
       do putStrLn "Counterexample!"
          return (Just True)
      else
        let mini =
              do qs' <- M.conflict (sat env)
                 let qs = [ Lit q | q <- qs' ] ++ [ p | (_,(p,_,_)) <- ws, p == tt ]
                 if null qs then
                   do putStrLn "Contradiction!"
                      return (Just False)
                  else
                   let p0:_ = [ p | (_,(p,_,_)) <- ws, p `elem` qs ] in
                     do verbose ("Conflict: " ++ show (length qs))
                        b <- if conflict_minimzation then
                               solveBit (sat env) (here env : reverse [ nt p | (_,(p,_,_)) <- ws, p `elem` qs, p /= p0 ])
                             else
                               return True
                        if b then
                          let (source,(p,unq,H h)):_ = [ t | t@(_,(p,_,_)) <- ws, p `elem` qs ] in
                            do let ws' = [ t | t@(_,(_,unq',_)) <- reverse ws, unq /= unq' ]
                               verbose ("Points: " ++ show (length ws'))
                               writeIORef (waits env) ws'
                               verbose $ "Expanding " ++ show source ++ "..."
                               h env{ here = p }
                               verbose "Expansion done"
                               return Nothing
                        else
                         do mini
         in mini
  )

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

solve' :: H () -> H Bool
solve' h =
  do h
     mb <- trySolve
     case mb of
       Nothing -> solve' h
       Just b  -> return b

solve :: H Bool
solve = solve' (return ())

getParams :: H Params
getParams = H (\env -> return (params env))

queryParam :: (Params -> a) -> H a
queryParam f = f <$> getParams

solveAndSee :: (Value a,Show (Type a),IncrView a) => a -> H ()
solveAndSee see =
  do incremental_view <- queryParam (not . quiet)
     b <- solve' (if incremental_view then io . putStrLn =<< incrView see else return ())
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
inContext c h = inContext' c h

inContext' :: Bit -> H a -> H a
inContext' c (H m) = H (\env -> m env{ here = c })

later :: Source -> Unique -> H () -> H ()
later source unq h = H (\env ->
  do ws <- readIORef (waits env)
     writeIORef (waits env) ((source, (here env, unq, h)):ws)
  )

{-
check :: H () -> H ()
check h@(H m) = H (\env ->
    do -- putStrLn "start"
       if here env == tt then
         m env
       else
         do cs <- readIORef (checks env)
            writeIORef (checks env) ((here env, h):cs)
       -- putStrLn "stop"
  )
-}

check :: H () -> H ()
check h =
  do u <- io newUnique
     later Check u h

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
unless cs h =
  do cs' <-
       filter (/= ff) <$>
       sequence
         [ case c of
             Bool b -> return c
             Lit l  ->
               do v <- withSolver (\ s -> M.value s l)
                  case v of
                    Nothing -> return c
                    Just b  -> do -- io (putStrLn "Knew an unless value!")
                                  return (if b then tt else ff)
         | c <- cs
         ]
     if null cs' then h
       else if tt `elem` cs' then do -- io (putStrLn "Knew it was false!")
                                     return ()
       else do c0 <- context
               c1 <- new
               -- [a1,a2, .. ,aN] = cs'
               -- ~a1 & ~a2 ... & ~aN => c1
               -- a1 | a2 | .. | aN | c1
               addClauseHere (c1:cs')
               inContext c1 $
                 do addClauseHere [c0]
                    -- in this context, all of a1...aN are false
                    sequence_ [ addClauseHere [nt c] | c <- cs' ]
                    h
 where
  cs' = filter (/=ff) cs

-- happens when one of them is true
whens :: [Bit] -> H () -> H ()
whens cs h =
  do cs' <-
       filter (/= ff) <$>
       sequence
         [ case c of
             Bool b -> return c
             Lit l  ->
               do v <- withSolver (\ s -> M.value s l)
                  case v of
                    Nothing -> return c
                    Just b  -> do -- io (putStrLn "Knew a value!")
                                  return (if b then tt else ff)
         | c <- cs
         ]
     if null cs' then return ()
       else if tt `elem` cs' then do -- io (putStrLn "Knew it was true!")
                                     h
       else do c0 <- context
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
  , invoke :: a -> H b
  }

newCall :: (Constructive a, Constructive b, Equal a, Equal b)
        => (a -> H (Maybe b)) -> H (Call a b)
newCall h =
  do b <- new
     x <- new
     c <- context
     my <- inContext' b $
       do addClauseHere [c]
          h x
     return $
       Call{ doit   = b
           , invoke = \x' -> do case my of
                                  Nothing -> error "Invoked Nothing!"
                                  Just y  -> do x' >>> x
                                                return y

           }

call :: Call a b -> a -> H b
call cl x =
  do addClauseHere [doit cl]
     invoke cl x

nocall :: Call a b -> H ()
nocall cl =
  do addClauseHere [nt (doit cl)]

--[ memo ]----------------------------------------------------------------------

nomemoWith :: Equal b => H b -> String -> (a -> b -> H ()) -> a -> H b
nomemoWith new_b tag h t =
  do r <- new_b
     h t r
     return r

{-# NOINLINE memoWith #-}
memoWith :: (Ord a, Equal b) => H b -> String -> (a -> b -> H ()) -> (a -> H b)
memoWith new_b tag h =
  unsafePerformIO $
    do -- putStrLn ("Creating table for " ++ tag ++ "...")
       ref <- newIORef Mp.empty
       return $
         \x -> do xys <- io $ readIORef ref
                  -- io $ putStrLn ("Table size for " ++ tag ++ ": " ++ show (Mp.size xys))
                  (c,y) <- case Mp.lookup x xys of
                             Nothing ->
                               do y <- new_b
                                  c <- new
                                  io $ writeIORef ref (Mp.insert x (c,y) xys)
                                  inContext c $ h x y
                                  return (c,y)

                             Just (c,y) ->
                               do --io $ putStrLn ("Duplicate call: " ++ tag)
                                  return (c,y)

                  addClauseHere [c]
                  return y

{-# NOINLINE memo #-}
memo :: (Ord a, Equal b, Constructive b) => String -> (a -> b -> H ()) -> (a -> H b)
memo = memoWith new

nomemo :: (Equal b, Constructive b) => String -> (a -> b -> H ()) -> a -> H b
nomemo = nomemoWith new

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
new      = do -- io (putStrLn "new")
              newPoint False
newInput = newPoint True

--------------------------------------------------------------------------------

class Equal a where
  (>>>)        :: a -> a -> H ()

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
  _ >>> _ = return ()
  equalHere    _ _ = return ()
  notEqualHere _ _ = addClauseHere []

instance Equal Bit where
  x >>> y = equalHere x y

  equalHere x y
    | x == y    = return ()
    | x == nt y = addClauseHere []
    | otherwise = do addClauseHere [nt x, y]
                     addClauseHere [nt y, x]

  notEqualHere x y = equalHere x (nt y)

instance (Equal a, Equal b) => Equal (a,b) where
  (x1,x2) >>> (y1,y2) =
    do x1 >>> y1
       x2 >>> y2

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

data Thunk a = This a | Delay Bool Unique (IORef (Either (H ()) a)) | Inaccessible

compareView :: Thunk a -> Maybe (Either a Unique)
compareView (This x)       = Just (Left x)
compareView (Delay _ u _)  = Just (Right u)
compareView (Inaccessible) = Nothing

instance Show a => Show (Thunk a) where
  show (This x)      = "This " ++ show x
  show (Delay b u r) = "Delay"
  show Inaccessible  = "Inaccessible"

instance Eq a => Eq (Thunk a) where
  (==) = (==) `on` compareView

instance Ord a => Ord (Thunk a) where
  compare = compare `on` compareView

this :: a -> Thunk a
this x = This x

delay :: Bool -> H a -> H (Thunk a)
delay inp (H m) =
  do c <- context
     ref <- io $ newIORef undefined
     io $ writeIORef ref (Left (H (\env -> m (env{ here = c }) >>= (writeIORef ref . Right))))
     unq <- io $ newUnique
     return (Delay inp unq ref)

inaccessible :: Thunk a
inaccessible = Inaccessible

poke :: Thunk a -> H ()
poke (This _)        = do return ()
poke Inaccessible    = addClauseHere []
poke (Delay _ _ ref) =
  do ema <- io $ readIORef ref
     case ema of
       Left m  -> m
       Right _ -> return ()

peek :: Thunk a -> H (Maybe a)
peek (This x)        = return (Just x)
peek Inaccessible    = return Nothing
peek (Delay _ _ ref) =
  do ema <- io $ readIORef ref
     return $ case ema of
       Left _  -> Nothing
       Right a -> Just a

force :: Thunk a -> H a
force th =
  do poke th
     ~(Just x) <- peek th
     return x

doForce :: Thunk a -> (a -> H ()) -> H ()
doForce t h = force t >>= h

ifForce :: Thunk a -> (a -> H ()) -> H ()
ifForce (This x)               h = h x
ifForce Inaccessible           h = addClauseHere []
ifForce th@(Delay inp unq ref) h =
  do ema <- io $ readIORef ref
     case ema of
       Left m  -> do c <- context
                     io $ writeIORef ref $ Left $
                       do m
                          Just a <- peek th
                          inContext c (h a)
                     if inp then
                       later Input unq $ poke th
                      else
                       return ()
       Right a -> h a

withoutForce :: a -> (a -> H ()) -> H ()
withoutForce x h = h x

instance Constructive a => Constructive (Thunk a) where
  newPoint inp = delay inp $ do -- io (putStrLn ("newThunk " ++ show inp))
                                newPoint inp


equ :: (a -> a -> H ()) -> Thunk a -> Thunk a -> H ()
equ k t1 t2 =
  do b <- queryParam strict_data_lazy_fun
     if b then check $ do a <- force t1
                          b <- force t2
                          k a b
          else ifForce t1 $ \a ->
               ifForce t2 $ \b ->
               k a b

instance Equal a => Equal (Thunk a) where
  t1 >>> t2 = equalThunk t1 t2

  equalHere = equ equalHere

  notEqualHere = equ notEqualHere

equalThunk :: forall a . Equal a => Thunk a -> Thunk a -> H ()
equalThunk x y = do
  -- io $ putStrLn "equalThunk"
  case (x, y) of
    (Delay _ u _, Delay _ v _)
      | u == v -> return ()
      | otherwise ->
         do equalUnique u v (equalThunk' x y)

    _ -> do equalThunk' x y
 where
  equalThunk' :: Thunk a -> Thunk a -> H ()
  equalThunk' x y =
    do ifForce x $ \a ->
         do b <- force y
            a >>> b

{-# NOINLINE equalUnique #-}
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
                      do -- io $ putStrLn "equalUnique"
                         return q
            addClauseHere [q]

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

--------------------------------------------------------------------------------

newtype Val a = Val [(Bit,a)] -- sorted on a
 deriving ( Eq, Ord )

instance Show a => Show (Val a) where
  show (Val xs) = "[" ++ concat (intersperse "," [ show x | (_,x) <- xs ]) ++ "]"

val :: a -> Val a
val x = Val [(tt,x)]

(=?),valEq :: Eq a => Val a -> a -> Bit
Val []         =? x  = ff
Val ((a,y):xs) =? x
  | x == y      = a
  | otherwise   = Val xs =? x
valEq = (=?)

valueToBit :: Bit -> H Bit
valueToBit (Bool b) = return (Bool b)
valueToBit (Lit b) = do u <- withSolver (\ s -> M.value s b)
                        case u of
                          Just b  -> return (if b then tt else ff)
                          Nothing -> return (Lit b)

(==?) :: Eq a => Val a -> a -> H Bit
Val []         ==? x  = return ff
Val ((a,y):xs) ==? x
  | x == y      = valueToBit a
  | otherwise   = do a' <- valueToBit a
                     if a' == tt then return ff else Val xs ==? x


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

valValue :: Val a -> H (Maybe a)
valValue (Val xs) = go xs
  where
  go [] = return Nothing
  go ((Bool b,a):xs) = if b then return (Just a) else go xs
  go ((Lit l,a):xs) =
    do v <- withSolver (\ s -> M.value s l)
       case v of
         Just True -> do -- io (putStrLn "Knew a valValue!")
                         return (Just a)
         _         -> go xs

instance Ord a => Equal (Val a) where
  (>>>) = equalHere

  equalHere l@(Val xs) r@(Val ys) =
   do ma <- valValue l
      mb <- valValue r
      case (ma,mb) of
        (Just a ,Just b)  -> addClauseHere [if a == b then tt else ff]
        (Just a ,Nothing) -> addClauseHere [r =? a]
        (Nothing,Just b)  -> addClauseHere [l =? b]
        (Nothing,Nothing) -> eq xs ys
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

data LiveDesc c
  = DataDesc String [c] [([c],LiveDesc c)]
  | ThunkDesc (LiveDesc c)
  deriving (Eq,Ord)

descTC :: LiveDesc c -> String
descTC (DataDesc tc _ _) = tc
descTC (ThunkDesc d)     = descTC d

instance Show c => Show (LiveDesc c) where
  show (DataDesc s cs xs) = s ++ " " ++ show cs ++ " " ++ show [(cs',descTC d)|(cs',d)<-xs]
  show (ThunkDesc d)      = "Thunk (" ++ show d ++ ")"

data LiveData c
  = LiveData String (Val c) [([c],Maybe (LiveData c))]
  | LiveThunk (Thunk (LiveData c))
  deriving (Eq,Ord,Show)

newData :: (Show c,Ord c) => Maybe Int -> Bool -> Bool -> LiveDesc c -> H (LiveData c)
newData (Just k) s i (ThunkDesc d)
  | k < 0 = return (LiveThunk inaccessible)

newData mk s i (ThunkDesc d)
  | s         = do (LiveThunk . this) <$> newData mk s i d
  | otherwise = do LiveThunk <$> delay i (newData mk s i d)

newData mk s i desc@(DataDesc tc cons args) =
  do c <- newVal cons
     as <- sequence [ do d <- newData (fmap (subtract 1) mk) s i desc
                         return (cs,Just d)
                    | (cs,desc) <- args
                    ]
     let d = LiveData tc c as
     -- io (print desc)
     -- io (print d)
     return d

equalLiveOn :: Ord c => (forall a . Equal a => a -> a -> H ()) -> LiveData c -> LiveData c -> H ()
equalLiveOn k (LiveThunk t1)        (LiveThunk t2)        = k t1 t2
equalLiveOn k (LiveData tc1 c1 as1) (LiveData tc2 c2 as2) = -- | tc1 == tc2 =
  do equalHere c1 c2
     ctx <- context

     let bigdmn = case domain c1 of
                    dmn@(_:_:_) -> Just (sort dmn)
                    _           -> Nothing

     sequence_
       [ case bigdmn of
           -- Just dmn | length cs * 2 > length dmn
           --   -> do let bs = [ c1 =? c | c <- sort dmn \\ sort cs ]
           --         io $ putStrLn (unwords ["UNLESS",show (length bs),show (length cs),show (length dmn)])
           --         unless bs (k x1 x2)
           _ -> do -- io $ putStrLn "WHENS"
                   ma <- valValue c1
                   mb <- valValue c2
                   case (ma,mb) of
                     (Just a ,Just b)  | a == b && a `elem` cs -> k x1 x2
                                       | otherwise      -> return ()
                     (Just a ,Nothing) | a `notElem` cs -> return ()
                     (Nothing,Just b)  | b `notElem` cs -> return ()
                     _ -> whens [ c1 =? c | c <- cs ] (k x1 x2)
       | ((cs,Just x1),(_cs,Just x2)) <- as1 `zip` as2
       ]

instance Ord c => Equal (LiveData c) where
  (>>>)        = equalLiveOn (>>>)
  equalHere    = equalLiveOn equalHere
  notEqualHere (LiveThunk th1)       (LiveThunk th2)       = notEqualHere th1 th2
  notEqualHere (LiveData tc1 c1 as1) (LiveData tc2 c2 as2) = -- | tc1 == tc2 =
    do -- io (putStrLn "notEqualHere")
       choice
         [ do notEqualHere c1 c2
         , do equalHere c1 c2
              choice
                [ do addClauseHere [ c1 =? c | c <- cs ]
                     notEqualHere x1 x2
                | ((cs,Just x1),(_cs,Just x2)) <- as1 `zip` as2
                ]
         ]

conData :: (Show c,Eq c) => LiveDesc c -> c -> [LiveData c] -> LiveData c
conData (ThunkDesc d)     c as =
  -- snd $ traceShowId $ (,) "conData" $
    LiveThunk (this (conData d c as))
conData (DataDesc s _ rs) c as =
  -- snd $ traceShowId $ (,) "conData" $
    LiveData s (val c)
      (snd
         (mapAccumL
           (\ as_rem (cs,_) ->
             if c `elem` cs then
               let hd:tl = as_rem
               in  (tl,(cs,Just hd))
             else
               (as_rem,(cs,Nothing))
           )
           as rs))

caseData :: LiveData c -> (Val c -> [LiveData c] -> H ()) -> H ()
caseData (LiveThunk th)      k = do b <- queryParam strict_data_lazy_fun
                                    if b then do ld <- force th
                                                 caseData ld k
                                         else ifForce th (\ ld -> caseData ld k)
caseData (LiveData _tc v vs) k = k v (map (\ (_,~(Just v)) -> v) vs)

data LiveValue c = ConValue c [LiveValue c] | ThunkValue

instance Eq c => Value (LiveData c) where
  type Type (LiveData c) = LiveValue c

  dflt _ = ThunkValue

  get (LiveThunk th)   = get th
  get (LiveData _ v cns) =
    do c <- get v
       as <- sequence [ get d | (cs,Just d) <- cns, c `elem` cs ]
       return (ConValue c as)

instance Show c => Show (LiveValue c) where
  show ThunkValue      = "_"
  show (ConValue g []) = show g
  show (ConValue g as) = "(" ++ show g ++ concat [ " " ++ show a | a <- as ] ++ ")"

instance Show c => IncrView (LiveData c) where
  incrView (LiveThunk th)      = incrView th
  incrView (LiveData tc _ cns) =
    do cns' <- sequence [ incrView mv | (_,mv) <- cns ]
       return ("(" ++ tc ++ concat cns' ++ ")")

-----------------------------------------------------------------

class IncrView a where
  incrView :: a -> H String

data Tagged a = Tagged [(String,a)]

instance IncrView a => IncrView (Tagged a) where
  incrView (Tagged [])         = return ""
  incrView (Tagged ((x,xe):r)) =
    do xe' <- incrView xe
       r'  <- incrView (Tagged r)
       return (x ++ ": " ++ xe' ++ "\n" ++ r')

instance Show a => Show (Tagged a) where
  show (Tagged xs) = unlines [ x ++ ": " ++ prettify (show xe) | (x,xe) <- xs ]

instance Value a => Value (Tagged a) where
  type Type (Tagged a) = Tagged (Type a)
  dflt _ = Tagged []
  get (Tagged xs) = Tagged <$> sequence [ (,) x <$> get xe | (x,xe) <- xs ]

data TagShow a b = TagCons String a b

data TagNil = TagNil

instance Show TagNil where
  show TagNil = ""

instance (Show a,Show b) => Show (TagShow a b) where
  show (TagCons x xe r) = x ++ ": " ++ show xe ++ "\n" ++ show r

instance IncrView TagNil where
  incrView TagNil = return ""

instance (IncrView a,IncrView b) => IncrView (TagShow a b) where
  incrView (TagCons x xe r) = do
    xe' <- incrView xe
    r' <- incrView r
    return (x ++ ": " ++ xe' ++ "\n" ++ r')

instance (Show a,IncrView a) => IncrView (Val a) where
  incrView (Val bs) =
    case [x | (tt,x) <- bs] of
      [x]    -> return (dropL_ (show x))
      ~(x:_) -> incrView x      -- the TyCon
   where
    dropL_ ('L':'_':l) = l
    dropL_ xs          = xs

instance IncrView a => IncrView (Maybe a) where
  incrView Nothing  = return "-"
  incrView (Just x) = incrView x

instance (IncrView a,IncrView b) => IncrView (a,b) where
  incrView (a,b) = (++) <$> incrView a <*> incrView b

instance IncrView () where
  incrView _ = return ""

instance IncrView a => IncrView (Thunk a) where
  incrView t =
    do md <- peek t
       case md of
         Nothing -> return "_"
         Just cn -> incrView cn

instance (Value a, Value b) => Value (TagShow a b) where
  type Type (TagShow a b) = TagShow (Type a) (Type b)
  dflt ~(TagCons _ x y) = TagCons "_" (dflt x) (dflt y)
  get   (TagCons s x y) = liftM2 (TagCons s) (get x) (get y)

instance Value (TagNil) where
  type Type TagNil = TagNil
  dflt _ = TagNil
  get  _ = return TagNil

-- Projection utilities

proj1 :: (Maybe a, z) -> a
proj1 (Just x, _) = x

proj2 :: (x, (Maybe a, z)) -> a
proj2 (_, (Just x, _)) = x

proj3 :: (x, (y, (Maybe a, z))) -> a
proj3 (_, (_, (Just x, _))) = x

proj4 :: (x1, (x, (y, (Maybe a, z)))) -> a
proj4 (_, (_, (_, (Just x, _)))) = x

proj5 :: (x2, (x1, (x, (y, (Maybe a, z))))) -> a
proj5 (_, (_, (_, (_, (Just x, _))))) = x

proj6 :: (x3, (x2, (x1, (x, (y, (Maybe a, z)))))) -> a
proj6 (_, (_, (_, (_, (_, (Just x, _)))))) = x

proj7 :: (x4, (x3, (x2, (x1, (x, (y, (Maybe a, z))))))) -> a
proj7 (_, (_, (_, (_, (_, (_, (Just x, _))))))) = x

proj8 :: (x5, (x4, (x3, (x2, (x1, (x, (y, (Maybe a, z)))))))) -> a
proj8 (_, (_, (_, (_, (_, (_, (_, (Just x, _)))))))) = x

unJust :: Maybe a -> a
unJust (Just x) = x
unJust Nothing  = error "unJust"

-- Prettify

prettify :: String -> String
prettify s = maybe s (undo . valToStr) (parseValue (esc s))
  where
  esc ('(':'_':s) = '(':'d':esc s
  esc (' ':'_':s) = ' ':'d':esc s
  esc (x:xs) = x:esc xs
  esc [] = []

  undo ('(':'d':s) = '(':'_':undo s
  undo (' ':'d':s) = ' ':'_':undo s
  undo (x:xs) = x:undo xs
  undo [] = []
