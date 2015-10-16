{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, MultiParamTypeClasses, FlexibleInstances, RankNTypes, FlexibleContexts #-}
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
import Data.Ord ( comparing )
import Data.Function ( on )

import Debug.Trace

import Text.Show.Pretty (parseValue,valToStr)

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
    do refw <- newIORef []
       m (Env s tt refw)

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

trySolve :: Bool -> Bool -> H (Maybe Bool)
trySolve confl_min quiet = H (\env ->
  do ws <- reverse `fmap` readIORef (waits env)
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
                        -- this can take a lot of time and doesn't necessarily help:
                        b <- if confl_min then
                               solveBit (sat env) (here env : reverse [ nt p | (_,(p,_,_)) <- ws, p `elem` qs, p /= p0 ])
                             else
                               return True
                        if b then
                          let (source,(p,unq,H h)):_ = [ t | t@(_,(p,_,_)) <- ws, p `elem` qs ] in
                            do let ws' = [ t | t@(_,(_,unq',_)) <- reverse ws, unq /= unq' ]
                               verbose ("Points: " ++ show (length ws'))
                               writeIORef (waits env) ws'
                               verbose $ "Expanding " ++ show source ++ "..." ++ show unq
                               h env{ here = p }
                               verbose "Expansion done"
                               return Nothing
                        else
                         do mini
         in mini
  )
 where
  verbose | quiet     = const (return ())
          | otherwise = putStrLn

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

solve' :: Bool -> Bool -> H () -> H Bool
solve' confl_min quiet h =
  do h
     mb <- trySolve confl_min quiet
     case mb of
       Nothing -> solve' confl_min quiet h
       Just b  -> return b

solve :: H Bool
solve = solve' False False (return ())

solveAndSee :: (Value a,Show (Type a),IncrView a) => Bool -> Bool -> Bool -> a -> H ()
solveAndSee confl_min quiet incremental_view see =
  do b <- solve' confl_min quiet (if incremental_view then io . putStrLn =<< incrView see else return ())
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
inContext c h = inContext' c h >> return ()

inContext' :: Bit -> H a -> H (Maybe a)
inContext' c _     | c == ff = return Nothing
inContext' c (H m) = H (\env -> Just <$> m env{ here = c })

inContext'' :: Bit -> H a -> H a
inContext'' c (H m) = H (\env -> m env{ here = c })

instance Show Unique where
  show = show . hashUnique

later :: Source -> Unique -> H () -> H ()
later source unq h = H (\env ->
  do ws <- readIORef (waits env)
     putStrLn $ "later " ++ show unq
     writeIORef (waits env) ((source, (here env, unq, h)):ws)
  )

check :: H (Delayed a) -> H (Delayed a)
check h =
  do t <- delay True (return ())
     after (React t) (\ _ -> h)

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

when :: Bit -> H a -> H (Maybe a)
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
whens :: [Bit] -> H a -> H (Maybe a)
whens cs h
  | null cs'  = return Nothing
  | otherwise =
    do c0 <- context
       c1 <- new
       sequence_ [ addClauseHere [nt c, c1] | c <- cs' ]
                               -- c => c1
       inContext' c1 $
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

--[ memo ]----------------------------------------------------------------------

{-# NOINLINE memo #-}
memo :: Ord a => String -> (a -> H b) -> (a -> H b)
memo tag h =
  unsafePerformIO $
    do -- putStrLn ("Creating table for " ++ tag ++ "...")
       ref <- newIORef Mp.empty
       return $
         \x -> do xys <- io $ readIORef ref
                  -- io $ putStrLn ("Table size for " ++ tag ++ ": " ++ show (Mp.size xys))
                  (c,y) <- case Mp.lookup x xys of
                             Nothing ->
                               do c <- new
                                  Just y <- inContext' c $ h x
                                  io $ writeIORef ref (Mp.insert x (c,y) xys)
                                  return (c,y)

                             Just (c,y) ->
                               do --io $ putStrLn ("Duplicate call: " ++ tag)
                                  return (c,y)

                  addClauseHere [c]
                  return y

nomemo :: String -> (a -> H b) -> a -> H b
nomemo _ = id

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

data Thunk a = This a | Delay Bool Unique (IORef (Either (H ()) a))

compareView :: Thunk a -> Either a Unique
compareView (This x)      = Left x
compareView (Delay _ u _) = Right u

uniqueView :: Thunk a -> Maybe Unique
uniqueView (This x)       = Nothing
uniqueView (Delay _ u _ ) = Just u

instance Show a => Show (Thunk a) where
  show (This x)      = "(This " ++ show x ++ ")"
  show (Delay b u r) = "(Delay " ++ show b ++ " " ++ show u ++ ")"


instance Eq a => Eq (Thunk a) where
  This x      == This y      = x == y
  Delay _ p _ == Delay _ q _ = p == q
  _           == _           = False

instance Ord a => Ord (Thunk a) where
  This x      `compare` This y      = x `compare` y
  Delay _ p _ `compare` Delay _ q _ = p `compare` q
  This _      `compare` _           = LT
  _           `compare` This _      = GT

{-
instance Eq a => Eq (Thunk a) where
  (==) = (==) `on` compareView

instance Ord a => Ord (Thunk a) where
  compare = compare `on` compareView
-}

this :: a -> Thunk a
this x = This x

delay :: Bool -> H a -> H (Thunk a)
delay inp (H m) =
  do c <- context
     ref <- io $ newIORef undefined
     unq <- io $ newUnique
     io $ writeIORef ref $ Left $ H $ \env -> do x <- debugIO (show unq) (m (env{ here = c }))
                                                 writeIORef ref (Right x)
     io $ putStrLn $ show unq ++ " created and delayed."
     let d = Delay inp unq ref
     return d

newtype React a = React (Thunk a)
  deriving (Eq,Ord,Show,Equal,IncrView)

instance Value a => Value (React a) where
  type Type (React a) = Type a
  dflt (React x) = dflt x
  get (React x) = get x

unforce :: Thunk a -> React a
unforce = React

reactThis :: a -> React a
reactThis = React . this

after :: React a -> (a -> H (React b)) -> H (React b)
after (React (This a))   k = k a
after (React ta@(Delay _ tunq _)) k =
  do c <- context
     ref <- io $ newIORef undefined
     unq <- io newUnique
     io $ writeIORef ref $ Left $ return ()
     ifForce ta $
       \ a ->
         do React tb <- debug (show unq ++ " k") (inContext'' c (k a))
            debug (show unq ++ " " ++ show (uniqueView tb)) $ ifForce tb $
              \ b ->
                do Left m <- io (readIORef ref)
                   io (writeIORef ref (Right b))
                   io $ putStrLn $ show unq ++ " evaluated!"
                   inContext'' c m
     io $ putStrLn $ show unq ++ " scheduled after " ++ show tunq
     let d = React (Delay False unq ref)
     return d

reactJoin :: React (React a) -> H (React a)
reactJoin rr = after rr return

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

enqueue :: Thunk a -> H ()
enqueue This{} = return ()
enqueue th@(Delay inp unq ref) =
  do ema <- io $ readIORef ref
     case ema of
       Left{} | inp -> later Input unq $ poke th
       _            -> return ()

ifForce :: Thunk a -> (a -> H ()) -> H ()
ifForce (This x)               h = h x
ifForce th@(Delay inp unq ref) h =
  do ema <- io $ readIORef ref
     enqueue th
     case ema of
       Left m  -> do c <- context
                     io $ writeIORef ref $ Left $
                       do debug (show unq ++ " ifForce") m
                          Just a <- peek th
                          debug (show unq ++ " ifForce context") (inContext c (h a))
       Right a -> h a

instance Constructive a => Constructive (Thunk a) where
  newPoint inp = delay inp $ do -- io (putStrLn ("newThunk " ++ show inp))
                                newPoint inp

instance Equal a => Equal (Thunk a) where
  t1 >>> t2 = equalThunk t1 t2

  equalHere t1 t2 =
    ifForce t1 $ \a ->
    ifForce t2 $ \b ->
      equalHere a b

  notEqualHere t1 t2 =
    ifForce t1 $ \a ->
    ifForce t2 $ \b ->
      notEqualHere a b

equalThunk :: Equal a => Thunk a -> Thunk a -> H ()
equalThunk x y = do
  -- io $ putStrLn "equalThunk"
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
  (>>>) = equalHere

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

data DataDesc c = DataDesc String [c] [([c],DataDesc c)]
  deriving (Eq,Ord)

descTC :: DataDesc c -> String
descTC (DataDesc tc _ _) = tc

instance Show c => Show (DataDesc c) where
  show (DataDesc s cs xs) = s -- ++ " " ++ show cs ++ " " ++ show [(cs',descTC d)|(cs',d)<-xs]

data Data c = Data String (Val c) [([c],Maybe (Delayed c))]
  deriving (Eq,Ord,Show)

type Delayed c = React (Data c)

newDelayed :: (Show c,Ord c) => Bool -> DataDesc c -> H (Delayed c)
newDelayed i d = React <$> delay i (newData i d)

newData :: (Show c,Ord c) => Bool -> DataDesc c -> H (Data c)
newData i desc@(DataDesc tc cons args) =
  do c <- newVal cons
     as <- sequence [ do d <- newDelayed i desc
                         return (cs,Just d)
                    | (cs,desc) <- args
                    ]
     let d = Data tc c as
     -- io (print desc)
     -- io (print d)
     return d

squash :: (Show a,Ord a) => [(Bit,Delayed a)] -> H (Delayed a)
squash = go . sortBy (comparing snd) . filter ((/= ff) . fst)
  where
  go [] = error $ "squash empty list: "
  go [(_,d)] = return d
  go ((b1,d1):(b2,d2):xs) =
    do d12 <- squashTwo b1 b2 d1 d2
       b12 <- orl [b1,b2]
       go ((b12,d12):xs)

squashTwo :: (Show a,Ord a) => Bit -> Bit -> Delayed a -> Delayed a -> H (Delayed a)
squashTwo b1 b2 t1 t2 -- use memo on unique here?
  | t1 == t2 = return t1 -- jinga!
  | otherwise
  = after t1 $ \ x1 ->
    after t2 $ \ x2 ->
    reactThis <$> squashTwoData b1 b2 x1 x2


squashTwoData :: (Show a,Ord a) => Bit -> Bit -> Data a -> Data a -> H (Data a)
squashTwoData b1 b2 (Data desc v1 as1) (Data _ v2 as2)
  = do v <- newVal (domain v1 `union` domain v2)
       let dom = domain v
       when b1 (equalHere v v1)
       when b2 (equalHere v v2)
       as <- sequence
         [ (,) cs <$> whens [ v =? c | c <- cs, c `elem` dom ]
                            (do case (m1,m2) of
                                  (Just x1,Just x2) -> squashTwo b1 b2 x1 x2
                                  (Nothing,Just x2) -> return x2
                                  (Just x1,Nothing) -> return x1
                                  (Nothing,Nothing) -> error "noone knows what the value is!")
         | ((cs,m1),(_cs,m2)) <- as1 `zip` as2
         ]
       return (Data desc v as)

equalOn :: Ord c => (forall a . Equal a => a -> a -> H ()) -> Data c -> Data c -> H ()
equalOn k (Data tc1 c1 as1) (Data tc2 c2 as2) = -- | tc1 == tc2 =
  do equalHere c1 c2
     sequence_
       [ whens [ c1 =? c | c <- cs ] (k x1 x2)
       | ((cs,Just x1),(_cs,Just x2)) <- as1 `zip` as2
       ]

instance Ord c => Equal (Data c) where
  (>>>)        = equalOn (>>>)
  equalHere    = equalOn equalHere
  notEqualHere (Data tc1 c1 as1) (Data tc2 c2 as2) = -- | tc1 == tc2 =
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

conDelayed :: (Show c,Eq c) => DataDesc c -> c -> [Delayed c] -> Delayed c
conDelayed desc c as = React (this (conData desc c as))

conData :: (Show c,Eq c) => DataDesc c -> c -> [Delayed c] -> Data c
conData desc@(DataDesc tc _ rs) c as =
  -- snd $ traceShowId $ (,) "conData" $
    Data tc (val c)
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

caseDelayed :: (Show c,Ord c) => Delayed c -> [(c,[Delayed c] -> H (Delayed c))] -> H (Delayed c)
caseDelayed r@(React t) ks =
  do after r $ \ a -> debug (show (uniqueView t) ++ " caseDelayed")
                            (caseData a ks)

caseData :: (Show c,Ord c) => Data c -> [(c,[Delayed c] -> H (Delayed c))] -> H (Delayed c)
caseData d@(Data _ v as) ks =
  do let as' = map (\ (_,mv) -> case mv of Just v -> v; Nothing -> error $ show d) as
     ds <-
       sequence
         [ (,) (v =? c) <$> when (v =? c) (debug (show c ++ " caseData") (k as'))
         | (c,k) <- ks
         ]
     debug "squash" $ squash [ (b,d) | (b,Just d) <- ds ]

debug :: String -> H a -> H a
debug s m = do
  io $ putStrLn $ s ++ " begin"
  x <- m
  io $ putStrLn $ s ++ " end"
  return x

debugIO :: String -> IO a -> IO a
debugIO s m = do
  putStrLn $ s ++ " begin"
  x <- m
  putStrLn $ s ++ " end"
  return x

data LiveValue c = ConValue c [LiveValue c] | ThunkValue

instance Eq c => Value (Data c) where
  type Type (Data c) = LiveValue c

  dflt _ = ThunkValue

  get (Data _ v cns) =
    do c <- get v
       as <- sequence [ get d | (cs,Just d) <- cns, c `elem` cs ]
       return (ConValue c as)

instance Show c => Show (LiveValue c) where
  show ThunkValue      = "_"
  show (ConValue g []) = show g
  show (ConValue g as) = "(" ++ show g ++ concat [ " " ++ show a | a <- as ] ++ ")"

instance Show c => IncrView (Data c) where
  incrView (Data tc _ cns) =
    do cns' <- sequence [ incrView mv | (_,mv) <- cns ]
       return ("(" ++ tc ++ concat cns' ++ ")")

-------------------------------------

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

    {-
instance (Show c,IncrView c,IncrView a) => IncrView (Data c a) where
  incrView (Con v c) =
    do v' <- incrView v
       c' <- incrView c
       return ("(" ++ v' ++ c' ++ ")")
       -}

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
