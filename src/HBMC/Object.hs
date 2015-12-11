{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module HBMC.Object where

--------------------------------------------------------------------------------------------

import qualified Data.Map as M
import Data.Map( Map )
import qualified Data.Set as S
import Data.Set( Set )
import Data.List( intercalate )
import Data.IORef
import Control.Applicative
import Control.Monad( when )
import System.IO( hFlush, stdout )

import SAT hiding ( false, true )
import qualified SAT

import Data.Function( on )
import HBMC.Params hiding ( memo )
import Tip.Utils( usortOn )

--------------------------------------------------------------------------------------------

type Name = String -- or whatever

class Names a where
  unkName   :: a
  unitName  :: a
  boolName  :: a
  falseName :: a
  trueName  :: a
  copyName  :: a
  equalHereName    :: a
  notEqualHereName :: a

instance Names Name where
  unkName   = "?"
  unitName  = "()"
  boolName  = "Bool"
  falseName = "False"
  trueName  = "True"
  copyName  = ">>>"
  equalHereName    = "equalHere"
  notEqualHereName = "notEqualHere"

--------------------------------------------------------------------------------------------

data Cons a = Cons a [Type a] (Type a)
 deriving Functor

instance Eq a => Eq (Cons a) where
  Cons c1 _ _ == Cons c2 _ _ = c1 == c2

instance Ord a => Ord (Cons a) where
  Cons c1 _ _ `compare` Cons c2 _ _ = c1 `compare` c2

instance Show a => Show (Cons a) where
  show (Cons c _ _) = show c

data Type a = Type a [Type a] [Cons a]
 deriving Functor

instance Eq a => Eq (Type a) where
  Type t1 a1 _ == Type t2 a2 _ = (t1,a1) == (t2,a2)

instance Ord a=> Ord (Type a) where
  Type t1 a1 _ `compare` Type t2 a2 _ = (t1,a1) `compare` (t2,a2)

instance Show a => Show (Type a) where
  show (Type t [] _) = show t
  show (Type t a  _) = show t ++ "(" ++ intercalate "," (map show a) ++ ")"

theArgs :: Eq n => Cons n -> [(Type n,a)] -> [a]
theArgs (Cons _ ts _) txs = find ts txs []
 where
  find []     _ _ = []
  find (t:ts) ((t',x):txs) txs'
    | t == t'     = x : find ts (reverse txs' ++ txs) []
    | otherwise   = find (t:ts) txs ((t',x):txs')

missingArgs :: Eq n => Cons n -> [(Type n,a)] -> [Type n]
missingArgs (Cons _ ts _) txs = find ts txs []
 where
  find []     _ _ = []
  find (t:ts) [] txs' = t : find ts (reverse txs') []
  find (t:ts) ((t',x):txs) txs'
    | t == t'     = find ts (reverse txs' ++ txs) []
    | otherwise   = find (t:ts) txs ((t',x):txs')

--------------------------------------------------------------------------------------------

unitT :: Names a => Type a
unitT = Type unitName [] [unit]

unit  :: Names a => Cons a
unit  = Cons unitName [] unitT

boolT :: Names a => Type a
boolT = Type boolName [] [false,true]

false, true :: Names a => Cons a
false = Cons falseName [] boolT
true  = Cons trueName  [] boolT

--------------------------------------------------------------------------------------------

data Object a
  = Static (Cons a) [Object a]
  | Dynamic Unique Bool {-input?-} (IORef (Contents a))

cmpView :: Object a -> Either (Cons a,[Object a]) Unique
cmpView (Static c os)   = Left (c,os)
cmpView (Dynamic u _ _) = Right u

instance Eq a => Eq (Object a) where
  (==) = (==) `on` cmpView

instance Ord a => Ord (Object a) where
  compare = compare `on` cmpView

data Contents a
  = Contents
  { alts    :: [(Cons a,Lit)]      -- alternatives already present
  , waits   :: [(Cons a,M a ())]   -- alternatives someone is waiting for
  , newCons :: M a ()              -- this callback will be run *once* when a new alternative becomes present
  , myType  :: Maybe (Type a)      -- do we already know the type of this object?
  , newType :: Type a -> M a ()    -- people waiting to get to know the type
  , args    :: [(Type a,Object a)] -- arguments to all constructors
  }

cons :: Cons a -> [Object a] -> Object a
cons c as = Static c as

new' :: Bool -> M a (Object a)
new' inp =
  do ref <- liftIO $ newIORef undefined
     unq <- newUnique
     let x = Dynamic unq inp ref
     liftIO $ writeIORef ref (Contents [] [] (return ()) Nothing (\_ -> return ()) [])
     return x

new :: M a (Object a)
new = new' False

newInput :: M a (Object a)
newInput = new' True

ifCons :: (Names a,Eq a) => Object a -> Cons a -> ([Object a] -> M a ()) -> M a ()
ifCons (Static c' xs) c h =
  if c' == c then h xs else return ()

ifCons obj@(Dynamic _ inp ref) c@(Cons _ _ t) h =
  do cnt <- liftIO $ readIORef ref
     ctx <- here
     case [ l | (c',l) <- alts cnt, c' == c ] of
       l:_ ->
         do withExtraContext l $ h (theArgs c (args cnt))

       _ ->
         do liftIO $ writeIORef ref cnt{ waits   = (c,wait) : filter ((/=c).fst) (waits cnt)
                                       , myType  = Just t
                                       , newType = \_ -> return ()
                                       }
            when inp $ enqueue obj
            case myType cnt of
              Nothing -> newType cnt t
              Just _  -> return ()
        where
         newwait =
           withNewContext ctx $
             do ifCons obj c h

         wait =
           case [ w | (c',w) <- waits cnt, c' == c ] of
             w:_ -> w >> newwait
             _   -> newwait

ifNotCons :: (Names a,Eq a) => Object a -> [Cons a] -> M a () -> M a ()
ifNotCons (Static c xs) cs h =
  if c `elem` cs then return () else h

ifNotCons obj@(Dynamic _ _ ref) cs h =
  do -- set up code h to run, and a trigger literal that says when the constraints should hold
     trig <- new
     l    <- withSolver newLit
     withNewContext l $
       ifCons trig unit $ \_ ->
         h

     let loop cs' =
           do cnt <- liftIO $ readIORef ref
              let someOther = any (\(c,_) -> c `notElem` cs) (alts cnt)
                  final     = all (\c -> c `elem` map fst (alts cnt)) cs

              -- if there exists a constructor that should trigger the code h
              when someOther $
                   -- run the code
                do isCons trig unit $ \_ -> return ()
                   -- add the clause that says when the constraints should hold
                   if final then
                     addClauseHere (l : [ l | (c,l) <- alts cnt, c `elem` cs ])
                    else
                     sequence_ [ addClauseHere [l, neg l']
                               | (c,l') <- alts cnt
                               , c `notElem` cs
                               , c `notElem` map fst cs'
                               ]

              -- please wake me up when a new constructor is added?
              when (not someOther || not final) $
                whenNewCons obj (loop (alts cnt))

      in loop []

proj_ :: Eq a => Object a -> Type a -> Int -> (Object a -> M a k) -> M a k -> M a k
proj_ (Static (Cons _ ts _) xs) t i h n
  | i < length as = h (as !! i)
  | otherwise     = error "proj_: out of bounds"
 where
  as = [ x | (t',x) <- ts `zip` xs, t' == t ]

proj_ obj@(Dynamic _ _ ref) t i h n =
  do cnt <- liftIO $ readIORef ref
     let as = [ x | (t',x) <- args cnt, t' == t ]
     if i < length as then
       h (as !! i)
      else
       n

unsafeProj :: Eq a => Object a -> Type a -> Int -> M a (Object a)
unsafeProj o t i =
  proj_ o t i return (error "unsafeProj: index out of bounds")

ifArg :: Eq a => Object a -> Type a -> Int -> (Object a -> M a ()) -> M a ()
ifArg o t i h =
  proj_ o t i h (whenNewCons o (ifArg o t i h))

isCons :: Eq a => Object a -> Cons a -> ([Object a] -> M a ()) -> M a ()
isCons (Static c' xs) c h =
  if c' == c then h xs else addClauseHere []

isCons obj@(Dynamic _ inp ref) c@(Cons _ _ t) h =
  do cnt <- liftIO $ readIORef ref
     l <- case [ l | (c',l) <- alts cnt, c' == c ] of
            l:_ ->
              do return l

            _ ->
              do l <- newLit' c (alts cnt)
                 let ts = missingArgs c (args cnt)
                 as <- sequence [ new' inp | t <- ts ]
                 liftIO $ writeIORef ref cnt{ alts    = (c,l) : alts cnt
                                            , waits   = filter ((/=c).fst) (waits cnt)
                                            , args    = args cnt ++ (ts `zip` as)
                                            , newCons = return ()
                                            , myType  = Just t
                                            , newType = \_ -> return ()
                                            }
                 sequence_ [ w | (c',w) <- waits cnt, c' == c ]
                 case myType cnt of
                   Nothing -> newType cnt t
                   Just _  -> return ()
                 newCons cnt
                 return l
     addClauseHere [l]
     cnt <- liftIO $ readIORef ref
     h (theArgs c (args cnt))
 where
  newLit' c@(Cons _ _ (Type _ _ alts)) pres
    | size == 1           = do return SAT.true
    | size == 2 && p == 1 = do return (neg (snd (head pres)))
    | otherwise           = do l <- withSolver newLit
                               withSolver $ \s -> sequence_ [ addClause s [neg l,neg l'] | (_,l') <- pres ]
                               sequence_ [ withSolver $ \s -> addClause s (l : map snd pres) | size == p+1 ]
                               return l
   where
    size = length alts
    p    = length pres

whenNewCons :: Object a -> M a () -> M a ()
whenNewCons (Static c _) h = return ()
whenNewCons (Dynamic _ _ ref) h =
  do cnt <- liftIO $ readIORef ref
     ctx <- here
     liftIO $ writeIORef ref cnt{ newCons = newCons cnt >> withNewContext ctx h }

ifType :: Object a -> (Type a -> M a ()) -> M a ()
ifType (Static (Cons _ _ t) _) h =
  do h t

ifType obj@(Dynamic _ _ ref) h =
  do cnt <- liftIO $ readIORef ref
     case myType cnt of
       Just t  -> do h t
       Nothing -> do ctx <- here
                     liftIO $ writeIORef ref cnt{ newType = \t -> newType cnt t >> withNewContext ctx (h t) }

isType :: Eq a => Object a -> Type a -> M a ()
isType (Static (Cons _ _ t') _) t | t' == t =
  do return ()

isType obj@(Dynamic _ _ ref) t =
  do cnt <- liftIO $ readIORef ref
     case myType cnt of
       Just t' | t == t' -> do return ()
       Nothing           -> do liftIO $ writeIORef ref cnt{ myType = Just t, newType = \_ -> return () }
                               newType cnt t

expand :: Eq a => Object a -> M a ()
expand (Static _ _) = return ()
expand obj@(Dynamic _ _ ref) =
  do cnt <- liftIO $ readIORef ref
     let Just (Type _ _ cs) = myType cnt
     sequence_ [ withNewContext SAT.false (isCons obj c $ \_ -> return ()) | c <- cs ]

--------------------------------------------------------------------------------------------

(>>>) :: (Names a,Ord a) => Object a -> Object a -> M a ()
o1 >>> o2 = do memo copyName (\[o1,o2] -> do copy o1 o2; return []) [o1,o2]; return ()
 where
  copy o1 o2 =
    do -- liftIO $ putStrLn "copy"
       ifType o2 $ \t ->
         isType o1 t

       ifType o1 $ \(Type _ _ cs) ->
         sequence_
         [ ifCons o1 c $ \xs ->
             isCons o2 c $ \ys ->
               sequence_ [ x >>> y | (x,y) <- xs `zip` ys ]
         | c <- cs
         ]

equalHere :: (Names a,Ord a) => Object a -> Object a -> M a ()
o1 `equalHere` o2 = do memo equalHereName (\[o1,o2] -> do go o1 o2; return []) [o1,o2]; return ()
 where
  go o1 o2 =
    do -- liftIO $ putStrLn "equalHere"
       ifType o2 $ \t ->
         isType o1 t

       ifType o1 $ \(Type _ _ cs) ->
         sequence_
         [ ifCons o1 c $ \xs ->
             do ifCons o2 c $ \ys ->
                  sequence_ [ x `equalHere` y | (x,y) <- xs `zip` ys ]
                ifNotCons o2 [c] (addClauseHere [])
         | c <- cs
         ]

notEqualHere :: (Names a,Ord a) => Object a -> Object a -> M a ()
o1 `notEqualHere` o2 = do memo notEqualHereName (\[o1,o2] -> do go o1 o2; return []) [o1,o2]; return ()
 where
  go o1 o2 =
    do -- liftIO $ putStrLn "notEqualHere"
       ifType o2 $ \t ->
         isType o1 t

       ifType o1 $ \(Type _ _ cs) ->
         sequence_
         [ ifCons o1 c $ \ xs ->
             ifCons o2 c $ \ ys ->
               choice (zipWith notEqualHere xs ys)
         | c <- cs
         ]

choice :: [M a ()] -> M a ()
choice [h] = h
choice hs =
  do xs <- sequence [ withSolver newLit | h <- hs ]
     addClauseHere xs
     a <- here
     sequence_ [ do withNewContext x (do addClauseHere [a]; h) | (x,h) <- xs `zip` hs ]

--------------------------------------------------------------------------------------------

memo, don'tMemo :: Ord a => a -> ([Object a] -> M a [Object a]) -> [Object a] -> M a [Object a]
memo name f xs =
  do tab <- getTable
     mp  <- liftIO $ readIORef tab
     (l,ys) <- case M.lookup (name,xs) mp of
                 Nothing ->
                   do l <- withSolver newLit
                      ys <- withNewContext l (f xs)
                      liftIO $ writeIORef tab (M.insert (name,xs) (l,ys) mp)
                      return (l,ys)

                 Just (l,ys) ->
                   do return (l,ys)
     addClauseHere [l]
     return ys

don'tMemo _name f xs = f xs

--------------------------------------------------------------------------------------------

later :: (Eq n,Names n) => M n () -> M n ()
later h =
  do x <- new' True
     ifCons x unit $ \_ -> h

--------------------------------------------------------------------------------------------

trySolve :: (Show n,Ord n) => Params -> M n (Maybe Bool)
trySolve params = M $ \env ->
  do lxs <- ordering `fmap` readIORef (queue env)
     as <- sequence [ let M m = objectView x in m env | (_,x) <- lxs ]
     when verbose $ putStr ("> solve: Q=" ++ show (length lxs) ++ " [" ++ intercalate ", " (nub as) ++ "]...")
     hFlush stdout
     b <- solve (solver env) [ neg l | (l,_) <- lxs ]
     if b then
       do putStrLn ""
          putStrLn "+++ SOLUTION"
          return (Just True)
     else
       do cs <- conflict (solver env)
          if null cs then
            do putStrLn ""
               putStrLn "*** NO SOLUTION"
               return (Just False)
           else
            do let x    = head [ x | (l,x) <- lxs, l `elem` cs ]
                   lxs' = reverse [ ly | ly@(_,y) <- lxs, y /= x ]
               writeIORef (queue env) lxs'
               when verbose $ putStrLn (" E=" ++ show (length lxs - length lxs'))
               let M m = expand x in m env
               -- these two lines are here because sometimes expansion adds an element
               -- to the queue that is going to be expanded in the same expansion
               lxs <- readIORef (queue env)
               writeIORef (queue env) [ q | q@(l,y) <- lxs, y /= x ]
               return Nothing
 where
  verbose = not (quiet params)

  ordering
    | age params = usortOn fst
    | otherwise  = nub . reverse

  nub xs = del S.empty xs
   where
    del seen [] = []
    del seen (x:xs) | x `S.member` seen = del seen xs
                    | otherwise         = x : del (S.insert x seen) xs

--------------------------------------------------------------------------------------------

data Val a = Cn (Cons a) [Val a] deriving ( Eq, Ord )

unkT :: Names a => Type a
unkT = Type unkName [] [unk]

unk :: Names a => Cons a
unk  = Cons unkName [] unkT

instance Show a => Show (Val a) where
  show (Cn c []) = show c
  show (Cn c xs) = show c ++ "(" ++ intercalate "," (map show xs) ++ ")"

objectVal :: (Names a,Eq a) => Object a -> M a (Val a)
objectVal (Static c xs) =
  do as <- sequence [ objectVal x | x <- xs ]
     return (Cn c as)

objectVal (Dynamic _ _ ref) =
  do cnt <- liftIO $ readIORef ref
     let alt [] =
           do return (Cn unk [])

         alt ((c,l):cls) =
           do b <- withSolver $ \s -> modelValue s l
              if b then
                do as <- sequence [ objectVal x | x <- theArgs c (args cnt) ]
                   return (Cn c as)
               else
                alt cls

      in alt (alts cnt)

objectView :: (Show a,Eq a) => Object a -> M a String
objectView (Static c xs) =
  do as <- sequence [ objectView x | x <- xs ]
     return ("!" ++ show c ++ "(" ++ intercalate "," as ++ ")")

objectView (Dynamic unq _ ref) =
  do cnt <- liftIO $ readIORef ref
     as <- sequence [ objectView x | (_,x) <- args cnt ]
     return $ case map (show . fst) (alts cnt) of
       []  -> show unq ++ "?"
       [c] -> show unq ++ c ++ "(" ++ intercalate "," as ++ ")"
       cs  -> show unq ++ "{" ++ intercalate "|" cs ++ "}(" ++ intercalate "," as ++ ")"

--------------------------------------------------------------------------------------------

data Env a =
  Env{ solver  :: Solver
     , context :: Lit
     , unique  :: IORef Int
     , table   :: IORef (Map (a,[Object a]) (Lit,[Object a]))
     , queue   :: IORef [(Lit,Object a)]
     }

newtype M n a = M (Env n -> IO a)

instance Functor (M n) where
  f `fmap` M h = M (fmap f . h)

instance Applicative (M n) where
  pure x      = return x
  M f <*> M a = M (\env -> f env <*> a env)

instance Monad (M n) where
  return x  = M (\_   -> return x)
  M h >>= k = M (\env -> do x <- h env; let M h' = k x in h' env)

-- run function

run :: M n () -> IO ()
run (M m) =
  withNewSolver $ \s ->
    do refUnique <- newIORef 0
       refTable  <- newIORef M.empty
       refQueue  <- newIORef []
       let env = Env{ solver  = s
                    , context = SAT.true
                    , unique  = refUnique
                    , table   = refTable
                    , queue   = refQueue
                    }
       m env

-- operations

enqueue :: Object n -> M n ()
enqueue x = M $ \env ->
  do lxs <- readIORef (queue env)
     writeIORef (queue env) ((context env,x):lxs)

type Unique = Int

newUnique :: M n Unique
newUnique = M $ \env ->
  do n <- readIORef (unique env)
     let n' = n+1
     n' `seq` writeIORef (unique env) n'
     return n'

getTable :: M n (IORef (Map (n,[Object n]) (Lit,[Object n])))
getTable = M (return . table)

withSolver :: (Solver -> IO a) -> M n a
withSolver h = M (h . solver)

here :: M n Lit
here = M (return . context)

withNewContext :: Lit -> M n a -> M n a
withNewContext l (M h) = M (\env -> h env{ context = l })

-- derived

liftIO :: IO a -> M n a
liftIO io = withSolver $ \_ -> io

addClauseHere :: [Lit] -> M n ()
addClauseHere xs =
  do ctx <- here
     withSolver $ \s -> addClause s (neg ctx : xs)

withExtraContext :: Lit -> M n a -> M n a
withExtraContext l h =
  do l' <- withSolver newLit
     addClauseHere [neg l, l']
     withNewContext l' h

--------------------------------------------------------------------------------------------

