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
  , ctx   :: [Bit]
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
       m (Env s [] ref)

trySolve :: H (Maybe Bool)
trySolve =
  H $ \env -> 
    do ps <- readIORef (posts env)
       putStrLn ("==> Try solve with " ++ show (length ps) ++ " points...")
       putStrLn "Searching for real counter example..."
       b <- solveBit (sat env) ([ nt b | (b, _) <- ps ] ++ ctx env)
       if b then
         do return (Just True)
        else
         do putStrLn "Searching for contradiction..."
            b <- solveBit (sat env) (ctx env)
            if not b then
              do return (Just False)
             else
              do putStrLn "Finding expansion points..."
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
                                          let v = Lit $ head [ w | Lit w <- ws, w `elem` cfl ]
                                          vs <- musts w (filter (/=v) ws)
                                          return (v:vs)
                             in do vs <- musts w ws
                                   putStrLn ("Expanding " ++ show (length (w:vs)) ++ " points.")
                                   writeIORef (posts env) [ p | p@(l,_) <- ps, l `notElem` (w:vs) ]
                                   sequence_ [ m (env{ ctx = [] }) | (l,H m) <- ps, l `elem` (w:vs) ]
                                   return Nothing
                  in find (map fst (reverse ps))
  
solve :: H Bool
solve =
  do mb <- trySolve
     case mb of
       Nothing -> solve
       Just b  -> return b

postpone :: Bit -> H () -> H ()
postpone b m | b == tt = io (putStrLn "Ha, postpone my ass!") >> m
postpone b (H m) =
  inContext b $
    H $ \env ->
      do ps <- readIORef (posts env)
         let p = (b, H (\env' -> m env'{ ctx = ctx env })) -- ignoring future context
         writeIORef (posts env) (p:ps)

check :: H () -> H ()
check h =
  do ctx <- context
     b <- withSolver (\s -> solveBit s ctx)
     if b then h else return ()

io :: IO a -> H a
io m = H (\_ -> m)

withSolver :: (Solver -> IO a) -> H a
withSolver h = H (\env -> h (sat env))

inContext :: Bit -> H () -> H ()
inContext b (H m)
  | b == ff   = return ()
  | otherwise = H (\env -> m env{ ctx = b : ctx env })

context :: H [Bit]
context = H (\env -> return (ctx env))

here :: [Bit] -> H ()
here xs =
  do ctx <- context
     ctx ==> xs

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
  equal      :: a -> a -> H Bit
  equalOr    :: [Bit] -> a -> a -> H ()
  notEqualOr :: [Bit] -> a -> a -> H ()

  equal x y =
    do q <- newBit
       equalOr    [nt q] x y
       notEqualOr [q]    x y
       return q

  equalOr xs x y =
    do q <- equal x y
       addClause (q:xs)

  notEqualOr xs x y =
    do q <- equal x y
       addClause (nt q:xs)

instance Equal () where
  equalOr    _  _ _ = return ()
  notEqualOr xs _ _ = addClause xs

instance Equal Bit where
  equalOr xs x y
    | x == y    = return ()
    | x == nt y = addClause xs
    | otherwise = do addClause ([nt x, y] ++ xs)
                     addClause ([nt y, x] ++ xs)

  notEqualOr xs x y = equalOr xs x (nt y)

instance (Equal a, Equal b) => Equal (a,b) where
  equalOr xs (x1,x2) (y1,y2) = 
    do equalOr xs x1 y1
       equalOr xs x2 y2

  notEqualOr xs (x1,x2) (y1,y2) = 
    do q <- newBit
       notEqualOr (q:xs)    x1 y1
       notEqualOr (nt q:xs) x2 y2

--------------------------------------------------------------------------------

iff :: (Eq a, Equal a, Constructive a) => Bit -> a -> a -> H a
iff c x y
  | c == tt   = return x
  | c == ff   = return y
  | x == y    = return x
  | otherwise = do z <- new
                   equalOr [nt c] z x
                   equalOr [c]    z y
                   return z

equalHere, notEqualHere :: Equal a => a -> a -> H ()
equalHere x y =
  do ctx <- context
     equalOr (map nt ctx) x y

notEqualHere x y =
  do ctx <- context
     notEqualOr (map nt ctx) x y

--------------------------------------------------------------------------------

class Value a where
  type Type a
  get :: a -> H (Type a)

instance Value () where
  type Type () = ()
  get _ = return ()

instance (Value a, Value b) => Value (a,b) where
  type Type (a,b) = (Type a, Type b)
  get (x,y) = liftM2 (,) (get x) (get y)

instance Value Bit where
  type Type Bit = Bool
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
  do ctx0 <- context
     ref <- io $ newIORef (Left (H (\env -> m (env{ ctx = ctx0 }))))
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

block :: Bit -> Thunk a -> (a -> H ()) -> H ()
block b thk h | b == ff = return ()
block b thk h = 
  do mx <- peek thk
     case mx of
       Nothing -> postpone b (force thk >>= h)
       Just x  -> inContext b (h x)

instance Constructive a => Constructive (Thunk a) where
  new = delay new

instance Equal a => Equal (Thunk a) where
  equalOr    xs = zipThunk (newImpl xs) (equalOr xs)
  notEqualOr xs = zipThunk (newImpl xs) (notEqualOr xs)

newImpl [] = return tt
newImpl xs = do l <- newBit
                addClause (l:xs)
                return l

zipThunk :: H Bit -> (a -> b -> H ()) -> Thunk a -> Thunk b -> H ()
zipThunk cond f t1 t2 =
  do ma <- peek t1
     mb <- peek t2
     case (ma, mb) of
       (Nothing, Nothing) ->
         do l <- cond
            postpone l $
              do a <- force t1
                 b <- force t2
                 f a b
       
       _ ->
         do a <- force t1
            b <- force t2
            f a b

instance Value a => Value (Thunk a) where
  type Type (Thunk a) = Maybe (Type a)
  
  get (This x)    = Just `fmap` get x
  get (Delay ref) =
    do ema <- io $ readIORef ref
       case ema of
         Left _  -> return Nothing
         Right x -> Just `fmap` get x

--------------------------------------------------------------------------------

data List a = List Bit (Thunk (a, List a))

nil :: List a
nil = List ff (error "nil /= cons")

cons :: a -> List a -> List a
cons x xs = List tt (this (x,xs))

ifNil :: List a -> H () -> H ()
ifNil (List c _) h =
  do inContext (nt c) h

ifCons :: List a -> (a -> List a -> H ()) -> H ()
ifCons (List c thk) h =
  do block c thk (uncurry h)

isNil :: List a -> H () -> H ()
isNil (List c _) h =
  do here [nt c]
     inContext (nt c) h

isCons :: List a -> (a -> List a -> H ()) -> H ()
isCons (List c thk) h =
  do here [c]
     inContext c $
       do (x,xs) <- force thk
          h x xs

newList :: Constructive a => Int -> H a -> H (List a)
newList 0 m =
  do return nil

newList k m =
  do c <- new
     x <- m
     xs <- newList (k-1) m
     return (List c (this (x,xs)))

instance Constructive a => Constructive (List a) where
  new = do c   <- new
           thk <- new
           return (List c thk)

instance Equal a => Equal (List a) where
  equalOr xs (List c1 t1) (List c2 t2) =
    do equalOr xs c1 c2
       if c1 == ff || c2 == ff then
         return ()
        else
         equalOr (nt c1 : nt c2 : xs) t1 t2

  notEqualOr xs (List c1 t1) (List c2 t2) =
    do addClause (c1 : c2 : xs)
       if c1 == ff || c2 == ff then
         return ()
        else
         notEqualOr (nt c1 : nt c2 : xs) t1 t2

{-
  equal xs ys =
    do q <- new
    
       ifNil xs $
         do ifNil  ys $         here [q]
            ifCons ys $ \_ _ -> here [nt q]
       
       ifCons xs $ \a as ->
         do ifNil ys $ here [nt q]
            ifCons ys $ \b bs ->
              do r  <- equal a b
                 rs <- equal as bs
                 here [nt r, nt rs, q]
                 here [r, nt q]
                 here [rs, nt q]
       
       return q
-}

instance Value a => Value (List a) where
  type Type (List a) = [Type a]
  
  get (List c thk) =
    do b <- get c
       if b then
         do Just (x,xs) <- get thk
            return (x:xs)
        else
         do return []

--------------------------------------------------------------------------------

data Fun a b = Fun (List (a,b)) b

apply :: (Equal a, Equal b) => Fun a b -> a -> b -> H ()
apply (Fun xys d) x y =
  do ifNil xys $
       equalHere y d
     
     ifCons xys $ \(a,b) abs ->
       do q <- equal a x
          inContext q $
            equalHere b y
          inContext (nt q) $
            apply (Fun abs d) x y

instance (Constructive a, Constructive b) => Constructive (Fun a b) where
  new =
    do (xys,d) <- new
       return (Fun xys d)

instance (Value a, Value b) => Value (Fun a b) where
  type Type (Fun a b) = ([(Type a, Type b)], Type b)

  get (Fun xys y) = get (xys,y)

--------------------------------------------------------------------------------

data Nat = Nat Bit (Thunk Nat)

nat :: Integer -> Nat
nat 0 = Nat ff (error "0 /= 1")
nat n = Nat tt (this (nat (n-1)))

ifZero :: Nat -> H () -> H ()
ifZero (Nat c _) h =
  do inContext (nt c) h

ifSucc :: Nat -> (Nat -> H ()) -> H ()
ifSucc (Nat c thk) h =
  do block c thk h

isZero :: Nat -> H () -> H ()
isZero (Nat c _) h =
  do here [nt c]
     inContext (nt c) h

isSucc :: Nat -> (Nat -> H ()) -> H ()
isSucc (Nat c thk) h =
  do here [c]
     inContext c $
       h =<< force thk

instance Constructive Nat where
  new = do c   <- new
           thk <- new
           return (Nat c thk)

instance Equal Nat where
  equalOr xs (Nat c1 t1) (Nat c2 t2) =
    do equalOr xs c1 c2
       if c1 == ff || c2 == ff then
         return ()
        else
         equalOr (nt c1 : nt c2 : xs) t1 t2

  notEqualOr xs (Nat c1 t1) (Nat c2 t2) =
    do addClause (c1 : c2 : xs)
       if c1 == ff || c2 == ff then
         return ()
        else
         notEqualOr (nt c1 : nt c2 : xs) t1 t2

instance Value Nat where
  type Type Nat = Integer
  
  get (Nat c thk) =
    do b <- get c
       if b then
         do Just n <- get thk
            return (n+1)
        else
         do return 0

--------------------------------------------------------------------------------

main = run $
  do io $ putStrLn "Generating problem..."
     --xs <- new :: H (List Nat)
     --ys <- new
     --zs <- new
     --xs <- newList 50 new :: H (List Bit)
     --ys <- newList 50 new
     --zs <- newList 20 new
     --xys <- new
     --yzs <- new
     --xyzs <- new
     --xyzs' <- new
     
     --p 10 (p 1 (\_ -> return ()) . bits) xs
     --p 10 (p 1 (\_ -> return ()) . bits) ys
     --p 10 (p 1 (\_ -> return ()) . bits) zs

     --p 10 (\_ -> return ()) xs
     --p 10 (\_ -> return ()) ys
     --p 10 (\_ -> return ()) zs
     
     --app xs ys xys
     --app xys zs xyzs
     --app ys zs yzs
     --app xs yzs xyzs'
     --notEqualHere xyzs xyzs'
     
     --rev xs ys
     --app xs ys zs
     --notEqualHere xs ys
     
     xs <- new :: H (List Nat)
     ys <- new
     snub xs xs
     f <- new
     smap f xs ys
     equalHere ys (cons (nat 1) (cons (nat 2) (cons (nat 3) nil)))
     let see = ((xs, ys), f)
     
     --xs <- new :: H (List Nat)
     --snub xs xs
     --isCons xs $ \_ as ->
     --  isCons as $ \_ bs ->
     --    isCons bs $ \_ cs ->
     --      isCons cs $ \_ _ -> return ()
     --let see = xs
     
     --n <- new :: H Nat
     --m <- new
     --notEqualHere n m
     --equalHere n m
     --let see = (n,m)
     
     --rs <- new
     --ssort xs rs
     --ssort ys rs
     --notEqualHere xs ys
     --notEqualHere xs rs
     --notEqualHere ys rs
     --rev xs zs
     --notEqualHere zs ys
     
     io $ putStrLn "Solving..."
     b <- solve
     io $ print b
     if b then
       do get see >>= (io . print)
      else
       do return ()

app xs ys zs =
  do ifNil xs $
       equalHere ys zs

     ifCons xs $ \a as ->
       isCons zs $ \b bs ->
         do equalHere a b
            app as ys bs
            
rev xs ys =
  do ifNil xs $
       isNil ys $
         return ()

     ifCons xs $ \a as ->
       do bs <- new
          rev as bs
          app bs (cons a nil) ys

qrev xs ys zs =
  do ifNil xs $
       equalHere ys zs

     ifCons xs $ \a as ->
       qrev as (cons a ys) zs

sinsert x xs zs =
  do ifNil xs $
       equalHere (cons x xs) zs
       
     ifCons xs $ \a as ->
       do leq <- orl [nt x, a]
          inContext leq $
            equalHere (cons x xs) zs
          inContext (nt leq) $
            isCons zs $ \b bs ->
              do sinsert x as bs
                 equalHere a b

ssort xs zs =
  do ifNil xs $
       isNil zs $
         return ()
     
     ifCons xs $ \a as ->
       do ws <- new
          ssort as ws
          sinsert a ws zs

snub xs zs =
  do ifNil xs $
       isNil zs $
         return ()
     
     ifCons xs $ \a as ->
       isCons zs $ \b bs ->
         do cs <- new
            sdelete a as cs
            snub cs bs
            equalHere a b

sdelete x xs zs =
  do ifNil xs $
       isNil zs $
         return ()
     
     ifCons xs $ \a as ->
       do q <- equal x a
          rs <- new
          sdelete x as rs
          inContext q $
            equalHere rs zs
          inContext (nt q) $
            isCons zs $ \b bs ->
              do equalHere a b
                 equalHere bs rs 

p 0 l xs = isNil xs $ return ()
p k l xs = ifCons xs $ \y ys -> do l y; p (k-1) l ys

smap f xs zs =
  do ifNil xs $
       isNil zs $
         return ()
     
     ifCons xs $ \y ys ->
       isCons zs $ \v vs ->
         do apply f y v
            smap f ys vs

