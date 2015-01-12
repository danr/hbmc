{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving #-}
module Main where

import Control.Applicative
import Control.Monad
import Data.IORef
import Data.List
import qualified MiniSat as M
import MiniSat ( Solver, Lit )

--------------------------------------------------------------------------------

data Env =
  Env
  { sat   :: Solver
  , here  :: Bit
  , posts :: IORef [(Bit,H ())] -- reversed queue
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
trySolve =
  H $ \env -> 
    do ps <- readIORef (posts env)
       putStrLn ("==> Try solve with " ++ show (length ps) ++ " points...")
       putStrLn "Searching for real counter example..."
       b <- solveBit (sat env) (here env : [ nt b | (b, _) <- ps ])
       if b then
         do return (Just True)
        else
         do putStrLn "Searching for contradiction..."
            b <- solveBit (sat env) [here env]
            if not b then
              do return (Just False)
             else
              do -- QUESTION: Should "here env" be assumed in the below calls to solve??
                 putStrLn "Finding expansion points..."
                 let find (w:ws) =
                       do b <- solveBit (sat env) [w]
                          if not b then
                            do putStrLn "Thrown away a point!"
                               find ws
                           else
                            let musts w ws =
                                  do b <- solveBit (sat env) (w : [ nt w | w <- ws ])
                                     if b then
                                       do return []
                                      else
                                       do cfl <- M.conflict (sat env)
                                          let v = head [ w | w <- ws, w `elem` map Lit cfl || w == tt ]
                                          vs <- musts w (filter (/=v) ws)
                                          return (v:vs)
                             in do vs <- musts w ws
                                   putStrLn ("Expanding " ++ show (length (w:vs)) ++ " points.")
                                   writeIORef (posts env) [ p | p@(l,_) <- ps, l `notElem` (w:vs) ]
                                   sequence_ [ m (env{ here = l }) | (l,H m) <- ps, l `elem` (w:vs) ]
                                   return Nothing
                  in find (map fst (reverse ps))
  
solve :: H Bool
solve =
  do mb <- trySolve
     case mb of
       Nothing -> solve
       Just b  -> return b

postpone :: H () -> H ()
postpone m =
  H $ \env ->
    do ps <- readIORef (posts env)
       let p = (here env, m)
       writeIORef (posts env) (p:ps)

check :: H () -> H ()
check h =
  do c <- context
     b <- withSolver (\s -> solveBit s [c])
     if b then h else return ()

io :: IO a -> H a
io m = H (\_ -> m)

withSolver :: (Solver -> IO a) -> H a
withSolver h = H (\env -> h (sat env))

context :: H Bit
context = H (\env -> return (here env))

inContext :: Bit -> H () -> H ()
inContext c _ | c == ff = return ()
inContext c (H m) = H (\env -> m env{ here = c })

must :: Bit -> H () -> H ()
must x h =
  do addClauseHere [x]
     if x == ff then return () else h

addClauseHere :: [Bit] -> H ()
addClauseHere xs =
  do c <- context
     [c] ==> xs

choice :: [H ()] -> H ()
choice hs =
  do xs <- sequence [ newBit | h <- hs ]
     addClauseHere xs
     sequence_ [ inContext x h | (x,h) <- xs `zip` hs ]

--------------------------------------------------------------------------------

class Constructive a where
  new :: H a

instance Constructive () where
  new = return ()

instance Constructive Bit where
  new = newBit

instance (Constructive a, Constructive b) => Constructive (a,b) where
  new = liftM2 (,) new new

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
  | otherwise    = do withSolver (\s -> M.addClause s [ x | Lit x <- xs ])
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

data Thunk a = This a | Delay (IORef (Either (H a) a))

this :: a -> Thunk a
this x = This x

delay :: H a -> H (Thunk a)
delay (H m) =
  do c <- context
     ref <- io $ newIORef (Left (H (\env -> m (env{ here = c }))))
     return (Delay ref)

peek :: Thunk a -> H (Maybe a)
peek (This x)    = return (Just x)
peek (Delay ref) =
  do ema <- io $ readIORef ref
     return $ case ema of
       Left _  -> Nothing
       Right a -> Just a

force :: Thunk a -> H a
force (This x)    = return x
force (Delay ref) =
  do ema <- io $ readIORef ref
     case ema of
       Left m  -> do a <- m -- uses the context of the delay
                     io $ writeIORef ref (Right a)
                     return a
       Right a -> do return a

instance Constructive a => Constructive (Thunk a) where
  new = delay new

instance Equal a => Equal (Thunk a) where
  equalHere    = zipThunk equalHere
  notEqualHere = zipThunk notEqualHere

zipThunk :: (a -> b -> H ()) -> Thunk a -> Thunk b -> H ()
zipThunk f t1 t2 =
  do ma <- peek t1
     mb <- peek t2
     case (ma, mb) of
       (Nothing, Nothing) ->
         postpone $
           do a <- force t1
              b <- force t2
              f a b
       
       _ ->
         do a <- force t1
            b <- force t2
            f a b

{-
zipThunk :: (a -> b -> H ()) -> Thunk a -> Thunk b -> H ()
zipThunk f t1 t2 =
  postpone $
    do a <- force t1
       b <- force t2
       f a b
-}

instance Value a => Value (Thunk a) where
  type Type (Thunk a) = Type a
  
  dflt x = dflt (unThunk x)
   where
    unThunk :: Thunk a -> a
    unThunk ~(This x) = x
  
  get (This x)    = get x
  get (Delay ref) =
    do ema <- io $ readIORef ref
       case ema of
         Left _  -> return (dflt (either undefined id ema))
         Right x -> get x

--------------------------------------------------------------------------------

type List a = Thunk (L a)
data L a    = L Bit (a, List a)

nil :: List a
nil = this (L ff (error "nil"))

cons :: a -> List a -> List a
cons x xs = this (L tt (x,xs))

isNil :: List a -> H () -> H ()
isNil xs h =
  do L c _ <- force xs
     must (nt c) $ h

isCons :: List a -> (a -> List a -> H ()) -> H ()
isCons xs h =
  do L c ~(y,ys) <- force xs
     must c $ h y ys

instance Constructive a => Constructive (L a) where
  new = do c   <- new
           xxs <- new
           return (L c xxs)

instance Equal a => Equal (L a) where
  equalHere (L c1 t1) (L c2 t2) =
    do equalHere c1 c2
       if c1 == ff || c2 == ff then
         return ()
        else
         do x <- new
            addClauseHere [nt c1, nt c2, x]
            inContext x $ equalHere t1 t2
  
  notEqualHere (L c1 t1) (L c2 t2) =
    do addClauseHere [c1, c2]
       if c1 == ff || c2 == ff then
         return ()
        else
         do x <- new
            addClauseHere [nt c1, nt c2, x]
            inContext x $ notEqualHere t1 t2
  
instance Value a => Value (L a) where
  type Type (L a) = [Type a]
  
  dflt _ = []
  
  get (L c xxs) =
    do b <- get c
       if b then
         do (x,xs) <- get xxs
            return (x:xs)
        else
         do return []

--------------------------------------------------------------------------------

data N = N Bit Nat
type Nat = Thunk N

nat :: Integer -> Nat
nat 0 = this (N ff undefined)
nat n = this (N tt (nat (n-1)))

isZero :: Nat -> H () -> H ()
isZero n h =
  do N c _ <- force n
     must (nt c) $ h

isSucc :: Nat -> (Nat -> H ()) -> H ()
isSucc n h =
  do N c ~n' <- force n
     must c $ h n'

instance Constructive N where
  new = do c <- new
           n <- new
           return (N c n)

instance Equal N where
  equalHere (N c1 t1) (N c2 t2) =
    do equalHere c1 c2
       if c1 == ff || c2 == ff then
         return ()
        else
         do x <- new
            addClauseHere [nt c1, nt c2, x]
            inContext x $ equalHere t1 t2
  
  notEqualHere (N c1 t1) (N c2 t2) =
    do addClauseHere [c1, c2]
       if c1 == ff || c2 == ff then
         return ()
        else
         do x <- new
            addClauseHere [nt c1, nt c2, x]
            inContext x $ notEqualHere t1 t2
  
instance Value N where
  type Type N = Integer

  dflt _ = 0
  
  get (N c n) =
    do b <- get c
       if b then
         do n' <- get n
            return (n'+1)
        else
         do return 0

--------------------------------------------------------------------------------

data Tree a = Node a (Tree a) (Tree a) | Empty
 deriving ( Eq, Ord, Show )

data T a = T Bit (a, (TREE a, TREE a))
type TREE a = Thunk (T a)

empty :: TREE a
empty = this (T ff undefined)

node :: a -> TREE a -> TREE a -> TREE a
node x p q = this (T tt (x, (p, q)))

isEmpty :: TREE a -> H () -> H ()
isEmpty t h =
  do T c _ <- force t
     must (nt c) $ h

isNode :: TREE a -> (a -> TREE a -> TREE a -> H ()) -> H ()
isNode t h =
  do T c ~(x,(p,q)) <- force t
     must c $ h x p q

instance Constructive a => Constructive (T a) where
  new = do c <- new
           t <- new
           return (T c t)

instance Equal a => Equal (T a) where
  equalHere (T c1 t1) (T c2 t2) =
    do equalHere c1 c2
       if c1 == ff || c2 == ff then
         return ()
        else
         do x <- new
            addClauseHere [nt c1, nt c2, x]
            inContext x $ equalHere t1 t2
  
  notEqualHere (T c1 t1) (T c2 t2) =
    do addClauseHere [c1, c2]
       if c1 == ff || c2 == ff then
         return ()
        else
         do x <- new
            addClauseHere [nt c1, nt c2, x]
            inContext x $ notEqualHere t1 t2
  
instance Value a => Value (T a) where
  type Type (T a) = Tree (Type a)

  dflt _ = Empty
  
  get (T c ~(x,(p,q))) =
    do b <- get c
       if b then
         do a <- get x
            s <- get p
            t <- get q
            return (Node a s t)
        else
         do return Empty

--------------------------------------------------------------------------------

main = main2

main1 = run $
  do io $ putStrLn "Generating problem..."
     xs <- new :: H (List Nat)
     ys <- new
     zs <- new
     isort xs zs
     isort ys zs
     
     notEqualHere xs zs
     notEqualHere ys zs
     notEqualHere xs ys
     
     let see = (xs,ys)

     io $ putStrLn "Solving..."
     b <- solve
     io $ print b
     if b then
       do get see >>= (io . print)
      else
       do return ()

main2 = run $
  do io $ putStrLn "Generating problem..."
     t <- new :: H (TREE Nat)
     
     member (nat 5) t tt
     member (nat 17) t tt
     member (nat 3) t tt
     member (nat 0) t ff
     
     let see = t

     io $ putStrLn "Solving..."
     b <- solve
     io $ print b
     if b then
       do get see >>= (io . print)
      else
       do return ()

app xs ys zs =
  choice
  [ isNil xs $
      equalHere ys zs

  , isCons xs $ \a as ->
      isCons zs $ \b bs ->
        do equalHere a b
           postpone $ app as ys bs
  ]
            
rev xs ys =
  choice
  [ isNil xs $
      isNil ys $
        return ()

  , isCons xs $ \a as ->
      do bs <- new
         postpone $ rev as bs
         app bs (cons a nil) ys
  ]

leq a b q =
  choice
  [ isZero a $
      addClauseHere [q]
  , isSucc a $ \a' ->
      choice
      [ isZero b $
          addClauseHere [nt q]
      , isSucc b $ \b' ->
          postpone $ leq a' b' q
      ]
  ]

sorted xs q =
  choice
  [ isNil xs $
      addClauseHere [q]
  , isCons xs $ \a as ->
      sorted' a as q
  ]

sorted' x xs q =
  choice
  [ isNil xs $
      addClauseHere [q]
  , isCons xs $ \a as ->
      do (q1,q2) <- new
         leq x a q1
         postpone $ sorted' a as q2
         addClauseHere [nt q1, nt q2, q]
         addClauseHere [nt q, q1]
         addClauseHere [nt q, q2]
  ]

sinsert x xs zs =
  choice
  [ isNil xs $
      isCons zs $ \b bs ->
        do equalHere x b
           isNil bs $
             return ()
  , isCons xs $ \a as ->
      do q <- new
         leq x a q
         choice
           [ do addClauseHere [q]
                isCons zs $ \b bs ->
                  do equalHere x b
                     equalHere xs bs
           , do addClauseHere [nt q]
                ys <- new
                postpone $ sinsert x as ys
                equalHere zs (cons a ys)
           ]
  ]

isort xs zs =
  choice
  [ isNil xs $
      isNil zs $
        return ()
  , isCons xs $ \a as ->
      do bs <- new
         postpone $ isort as bs
         sinsert a bs zs  
  ]

member x t w =
  choice
  [ isEmpty t $
      addClauseHere [nt w]
  , isNode t $ \a p q ->
      choice
      [ do equalHere x a
           addClauseHere [w]
      , do notEqualHere x a
           d <- new
           leq x a d
           pq <- new
           postpone $ member x pq w
           choice
             [ do addClauseHere [d]
                  equalHere pq p
             , do addClauseHere [nt d]
                  equalHere pq q
             ]
      ]
  ]

