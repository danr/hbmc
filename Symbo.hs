
import qualified Data.Map as M
import Data.Map( Map )
import Data.Maybe( fromJust )
import Data.List( intersperse )
import Data.IORef
import Data.Unique

import SAT

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
  show (Type t a  _) = t ++ "(" ++ concat (intersperse "," (map show a)) ++ ")"

--------------------------------------------------------------------------------------------

data Object
  = Static Cons [Object]
  | Dynamic Unique (IORef Contents)

instance Eq Object where
  o1 == o2 = o1 `compare` o2 == EQ

instance Ord Object where
  Static c1 a1 `compare` Static c2 a2 = (c1,a1) `compare` (c2,a2)
  Static _  _  `compare` Dynamic _ _  = LT
  Dynamic _ _  `compare` Static _ _   = GT
  Dynamic u1 _ `compare` Dynamic u2 _ = u1 `compare` u2

data Contents
  = Contents [(Cons,Lit)] [(Cons,M ())] (Cons -> [Object] -> M ()) [(Type,Object)]

cons :: Cons -> [Object] -> Object
cons c as = Static c as

new :: M Object
new = liftIO $
  do ref <- newIORef (Contents [] [] (\_ _ -> return ()) [])
     unq <- newUnique
     return (Dynamic unq ref)

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

ifAnyCons :: Object -> (Cons -> [Object] -> M ()) -> M ()
ifAnyCons (Static c xs)   h = h c xs
ifAnyCons (Dynamic _ ref) h =
  do Contents pres waits await args <- liftIO $ readIORef ref
     sequence_ [ withExtraContext l $ h c (theArgs c args) | (c,l) <- pres ]
     ctx <- here
     liftIO $ writeIORef ref (Contents pres waits (\c xs -> await c xs >> withNewContext ctx (h c xs)) args)

ifCons :: Object -> Cons -> ([Object] -> M ()) -> M ()
ifCons (Static c' xs) c h =
  if c' == c then h xs else return ()

ifCons obj@(Dynamic _ ref) c h =
  do Contents pres waits await args <- liftIO $ readIORef ref
     ctx <- here
     case [ l | (c',l) <- pres, c' == c ] of
       l:_ ->
         withExtraContext l $ h (theArgs c args)
       
       _ ->
         liftIO $ writeIORef ref (Contents pres ((c,wait):filter ((/=c).fst) waits) await args)
        where
         newWait =
           withNewContext ctx $
             do ifCons obj c h
         
         wait =
           case [ w | (c',w) <- waits, c' == c ] of
             w:_ -> w >> newWait
             _   -> newWait

isCons :: Object -> Cons -> ([Object] -> M ()) -> M ()
isCons (Static c' xs) c h =
  if c' == c then h xs else addClauseHere []

isCons obj@(Dynamic _ ref) c h =
  do Contents pres waits await args <- liftIO $ readIORef ref
     l <- case [ l | (c',l) <- pres, c' == c ] of
            l:_ ->
              do return l
              
            _ ->
              do l <- withSolver newLit
                 withSolver $ \s -> sequence_ [ addClause s [neg l,neg l'] | (_,l') <- pres ]
                 let ts = missingArgs c args
                 as <- sequence [ new | t <- ts ]
                 let args' = args ++ (ts `zip` as)
                 liftIO $ writeIORef ref (Contents ((c,l):pres) (filter ((/=c).fst) waits) await args')
                 sequence_ [ w | (c',w) <- waits, c' == c ]
                 await c (theArgs c args')
                 return l
     addClauseHere [l]
     h (theArgs c args)

(>>>) :: Object -> Object -> M ()
o1 >>> o2 = do memo ">>>" (\[o1,o2] -> do copy o1 o2; return []) [o1,o2]; return ()
 where
  copy o1 o2 =
    ifAnyCons o1 $ \c xs ->
      isCons o2 c $ \ys ->
        sequence_ [ x >>> y | (x,y) <- xs `zip` ys ]

data Env =
  Env{ solver  :: Solver
     , context :: Lit
     , table   :: IORef (Map (Name,[Object]) (Lit,[Object]))
     } 

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

newtype M a = M (Env -> IO a)

instance Functor M where
  f `fmap` M h = M (fmap f . h)

instance Monad M where
  return x  = M (\_   -> return x)
  M h >>= k = M (\env -> do x <- h env; let M h' = k x in h' env)

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

data Expr
  = Var Name
  | Con Cons [Expr]
  | App Name [Expr]
  | Let Name Expr Expr
  | LetApp Name [Name] Expr Expr
  | Case Expr [(Cons,[Name],Expr)]

type Program = Map Name ([Name],Expr)

--------------------------------------------------------------------------------------------

eval :: Program -> Map Name ([Object],Object) -> Map Name Object -> Expr -> M Object
eval prog apps env (Var x) =
  do return (fromJust (M.lookup x env))

eval prog apps env (Con c as) =
  do ys <- sequence [ eval prog apps env a | a <- as ]
     return (cons c ys)
     
eval prog apps env (App f as) =
  do ys <- sequence [ eval prog apps env a | a <- as ]
     let Just (xs,rhs) = M.lookup f prog
     eval prog M.empty (M.fromList (xs `zip` ys)) rhs

eval prog apps env (Let x a b) =
  do y <- eval prog apps env a
     eval prog apps (M.insert x y env) b

eval prog apps env (LetApp f xs a b) =
  undefined

eval prog apps env (Case a alts) =
  do res <- new
     evalInto prog apps env (Case a alts) res
     return res

--------------------------------------------------------------------------------------------

evalInto :: Program -> Map Name ([Object],Object) -> Map Name Object -> Expr -> Object -> M ()
evalInto prog apps env (Var x) res =
  do fromJust (M.lookup x env) >>> res

evalInto prog apps env (Con c as) res =
  do isCons res c $ \ys ->
       sequence_ [ evalInto prog apps env a y | (a,y) <- as `zip` ys ]

evalInto prog apps env (App f as) res =
  do ys <- sequence [ eval prog apps env a | a <- as ]
     let Just (xs,rhs) = M.lookup f prog
     evalInto prog M.empty (M.fromList (xs `zip` ys)) rhs res

evalInto prog apps env (Let x a b) res =
  do y <- eval prog apps env a
     evalInto prog apps (M.insert x y env) b res

evalInto prog apps env (LetApp f xs a b) res =
  undefined

evalInto prog apps env (Case a alts) res =
  do y <- eval prog apps env a
     sequence_
       [ ifCons y c $ \ys ->
           evalInto prog apps (foldr (\(x,y) -> M.insert x y) env (xs `zip` ys)) rhs res
       | (c,xs,rhs) <- alts
       ]
  
--------------------------------------------------------------------------------------------


