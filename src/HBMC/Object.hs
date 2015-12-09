module Object where

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

--------------------------------------------------------------------------------------------

type Name = String -- or whatever

--------------------------------------------------------------------------------------------

data Cons = Cons Name [Type] Type

instance Eq Cons where
  Cons c1 _ _ == Cons c2 _ _ = c1 == c2

instance Ord Cons where
  Cons c1 _ _ `compare` Cons c2 _ _ = c1 `compare` c2

instance Show Cons where
  show (Cons c _ _) = c

data Type = Type Name [Type] [Cons]

instance Eq Type where
  Type t1 a1 _ == Type t2 a2 _ = (t1,a1) == (t2,a2)

instance Ord Type where
  Type t1 a1 _ `compare` Type t2 a2 _ = (t1,a1) `compare` (t2,a2)

instance Show Type where
  show (Type t [] _) = t
  show (Type t a  _) = t ++ "(" ++ intercalate "," (map show a) ++ ")"

theArgs :: Cons -> [(Type,a)] -> [a]
theArgs (Cons _ ts _) txs = find ts txs []
 where
  find []     _ _ = []
  find (t:ts) ((t',x):txs) txs'
    | t == t'     = x : find ts (reverse txs' ++ txs) []
    | otherwise   = find (t:ts) txs ((t',x):txs')

missingArgs :: Cons -> [(Type,a)] -> [Type]
missingArgs (Cons _ ts _) txs = find ts txs []
 where
  find []     _ _ = []
  find (t:ts) [] txs' = t : find ts (reverse txs') []
  find (t:ts) ((t',x):txs) txs'
    | t == t'     = find ts (reverse txs' ++ txs) []
    | otherwise   = find (t:ts) txs ((t',x):txs')

--------------------------------------------------------------------------------------------

unitT = Type "()" [] [unit]
unit  = Cons "()" [] unitT

boolT = Type "Bool"  [] [false,true]
false = Cons "False" [] boolT
true  = Cons "True"  [] boolT

--------------------------------------------------------------------------------------------

data Object
  = Static Cons [Object]
  | Dynamic Unique Bool {-input?-} (IORef Contents)

instance Eq Object where
  o1 == o2 = o1 `compare` o2 == EQ

instance Ord Object where
  Static c1 a1   `compare` Static c2 a2   = (c1,a1) `compare` (c2,a2)
  Static _  _    `compare` Dynamic _ _ _  = LT
  Dynamic _ _ _  `compare` Static _ _     = GT
  Dynamic u1 _ _ `compare` Dynamic u2 _ _ = u1 `compare` u2

data Contents
  = Contents
  { alts    :: [(Cons,Lit)]    -- alternatives already present
  , waits   :: [(Cons,M ())]   -- alternatives someone is waiting for
  , newCons :: M ()            -- this callback will be run *once* when a new alternative becomes present
  , myType  :: Maybe Type      -- do we already know the type of this object?
  , newType :: Type -> M ()    -- people waiting to get to know the type
  , args    :: [(Type,Object)] -- arguments to all constructors
  }

cons :: Cons -> [Object] -> Object
cons c as = Static c as

new' :: Bool -> M Object
new' inp = 
  do ref <- liftIO $ newIORef undefined
     unq <- newUnique
     let x = Dynamic unq inp ref
     liftIO $ writeIORef ref (Contents [] [] (return ()) Nothing (\_ -> return ()) [])
     return x

new :: M Object
new = new' False

newInput :: M Object
newInput = new' True

ifCons :: Object -> Cons -> ([Object] -> M ()) -> M ()
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

ifNotCons :: Object -> [Cons] -> M () -> M ()
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

ifArg :: Object -> Type -> Int -> (Object -> M ()) -> M ()
ifArg (Static (Cons _ ts _) xs) t i h
  | i < length as = h (as !! i)
  | otherwise     = return ()
 where
  as = [ x | (t',x) <- ts `zip` xs, t' == t ] 

ifArg obj@(Dynamic _ _ ref) t i h =
  do cnt <- liftIO $ readIORef ref
     let as = [ x | (t',x) <- args cnt, t' == t ]
     if i < length as then
       h (as !! i)
      else
       whenNewCons obj (ifArg obj t i h)

isCons :: Object -> Cons -> ([Object] -> M ()) -> M ()
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

whenNewCons :: Object -> M () -> M ()
whenNewCons (Static c _) h = return ()
whenNewCons (Dynamic _ _ ref) h =
  do cnt <- liftIO $ readIORef ref
     ctx <- here
     liftIO $ writeIORef ref cnt{ newCons = newCons cnt >> withNewContext ctx h }

ifType :: Object -> (Type -> M ()) -> M ()
ifType (Static (Cons _ _ t) _) h =
  do h t

ifType obj@(Dynamic _ _ ref) h =
  do cnt <- liftIO $ readIORef ref
     case myType cnt of
       Just t  -> do h t
       Nothing -> do ctx <- here
                     liftIO $ writeIORef ref cnt{ newType = \t -> newType cnt t >> withNewContext ctx (h t) }

isType :: Object -> Type -> M ()
isType (Static (Cons _ _ t') _) t | t' == t =
  do return ()

isType obj@(Dynamic _ _ ref) t =
  do cnt <- liftIO $ readIORef ref
     case myType cnt of
       Just t' | t == t' -> do return ()
       Nothing           -> do liftIO $ writeIORef ref cnt{ myType = Just t, newType = \_ -> return () }
                               newType cnt t

expand :: Object -> M ()
expand (Static _ _) = return ()
expand obj@(Dynamic _ _ ref) =
  do cnt <- liftIO $ readIORef ref
     let Just (Type _ _ cs) = myType cnt
     sequence_ [ withNewContext SAT.false (isCons obj c $ \_ -> return ()) | c <- cs ]

--------------------------------------------------------------------------------------------

(>>>) :: Object -> Object -> M ()
o1 >>> o2 = do memo ">>>" (\[o1,o2] -> do copy o1 o2; return []) [o1,o2]; return ()
 where
  copy o1 o2 =
    do ifType o2 $ \t ->
         isType o1 t
       
       ifType o1 $ \(Type _ _ cs) ->
         sequence_
         [ ifCons o1 c $ \xs ->
             isCons o2 c $ \ys ->
               sequence_ [ x >>> y | (x,y) <- xs `zip` ys ]
         | c <- cs
         ]

--------------------------------------------------------------------------------------------

memo :: Name -> ([Object] -> M [Object]) -> [Object] -> M [Object]
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

--------------------------------------------------------------------------------------------

later :: M () -> M ()
later h =
  do x <- new' True
     ifCons x unit $ \_ -> h

--------------------------------------------------------------------------------------------

trySolve :: M (Maybe Bool)
trySolve = M $ \env ->
  do lxs <- (nub . reverse) `fmap` readIORef (queue env)
     as <- sequence [ let M m = objectView x in m env | (_,x) <- lxs ]
     putStr ("> solve: Q=" ++ show (length lxs) ++ " [" ++ intercalate ", " (nub as) ++ "]...")
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
               putStrLn (" E=" ++ show (length lxs - length lxs'))
               let M m = expand x in m env
               -- these two lines are here because sometimes expansion adds an element
               -- to the queue that is going to be expanded in the same expansion
               lxs <- readIORef (queue env)
               writeIORef (queue env) [ q | q@(l,y) <- lxs, y /= x ]
               return Nothing
 where
  nub xs = del S.empty xs
   where
    del seen [] = []
    del seen (x:xs) | x `S.member` seen = del seen xs
                    | otherwise         = x : del (S.insert x seen) xs

--------------------------------------------------------------------------------------------

data Val = Cn Cons [Val] deriving ( Eq, Ord )

unkT = Type "?" [] [unk]
unk  = Cons "?" [] unkT

instance Show Val where
  show (Cn c []) = show c
  show (Cn c xs) = show c ++ "(" ++ intercalate "," (map show xs) ++ ")"

objectVal :: Object -> M Val
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

objectView :: Object -> M String
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

data Env =
  Env{ solver  :: Solver
     , context :: Lit
     , unique  :: IORef Int
     , table   :: IORef (Map (Name,[Object]) (Lit,[Object]))
     , queue   :: IORef [(Lit,Object)]
     }

newtype M a = M (Env -> IO a)

instance Functor M where
  f `fmap` M h = M (fmap f . h)

instance Applicative M where
  pure x      = return x
  M f <*> M a = M (\env -> f env <*> a env)

instance Monad M where
  return x  = M (\_   -> return x)
  M h >>= k = M (\env -> do x <- h env; let M h' = k x in h' env)

-- run function

run :: M () -> IO ()
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

enqueue :: Object -> M ()
enqueue x = M $ \env ->
  do lxs <- readIORef (queue env)
     writeIORef (queue env) ((context env,x):lxs)

type Unique = Int

newUnique :: M Unique
newUnique = M $ \env ->
  do n <- readIORef (unique env)
     let n' = n+1
     n' `seq` writeIORef (unique env) n'
     return n'

getTable :: M (IORef (Map (Name,[Object]) (Lit,[Object])))
getTable = M (return . table)

withSolver :: (Solver -> IO a) -> M a
withSolver h = M (h . solver)

here :: M Lit
here = M (return . context)

withNewContext :: Lit -> M a -> M a
withNewContext l (M h) = M (\env -> h env{ context = l })

-- derived

liftIO :: IO a -> M a
liftIO io = withSolver $ \_ -> io

addClauseHere :: [Lit] -> M ()
addClauseHere xs =
  do ctx <- here
     withSolver $ \s -> addClause s (neg ctx : xs)

withExtraContext :: Lit -> M a -> M a
withExtraContext l h =
  do l' <- withSolver newLit
     addClauseHere [neg l, l']
     withNewContext l' h

--------------------------------------------------------------------------------------------

