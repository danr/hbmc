module HBMC.Chameleon where

type N v = StateT (Env v) Z3

z3 :: Z3 a -> N v a
z3 = lift

io :: IO a -> N v a
io = liftIO

data Env v =
  Env
  -- global:
  { next   :: Int
  , memo   :: Map (v,[Object v]) (Object v)
  , queue  :: [(AST,N v ())]
  , splits :: Map AST [(v,Object v)]

  -- local:
  , ctx    :: AST
  , names  :: Map v (Object v)
  , apps   :: Map v ([AST],Object v,N v ())

  -- read only:
  , sigs   :: Map v FuncDecl     -- including constructors and projections
  , funcs  :: Map v ([v],Expr v)
  , domain :: Sort
  }

#define modLabel(label) (\ f x -> x { label = f (label x) })
#define modM(label)     (modify modLabel(label))

runOnce :: N v () -> N v (N v ())
runOnce m =
  do ref <- io (newIORef False)
     return $
       do been_run <- io (readIORef ref)
          if been_run
            then return ()
            else io (writeIORef ref True) >> m

localNames :: (Map v AST -> Map v AST) ->  N v a -> N v a
localNames f m =
  do ns <- gets names
     modM(names) f
     x <- m
     modM(names) (const ns)
     return x

saveLocals :: N v (Env v -> Env v)
saveLocals m =
  do c  <- gets ctx
     ns <- gets names
     as <- gets apps
     return (\ e -> e { ctx = c, names = ns, apps = as })

enqueue :: N v () -> N v ()
enqueue m =
  do f <- saveLocals
     x <- gets ctx
     modM(queue) ((x,do modify f >> m):)

fresh :: N v Int
fresh =
  do x <- gets next
     modM(next) (+1)
     return x

freshSymbol :: N v Symbol
freshSymbol = z3 . mkIntSymbol =<< fresh

assertHere :: AST -> N v ()
assertHere e =
  do x <- gets ctx
     assert =<< z3 (mkImplies x e)

assert :: AST -> N v ()
assert = z3 . solverAssertConstr

equalHere :: Object v -> Object v -> N v ()
equalHere a b = equalASTHere (objectAst a) (objectAst b)

equalASTHere :: AST -> AST -> N v ()
equalASTHere a b = assertHere =<< z3 (mkEq a b)

-- variables (which are actually constants)
freshVar :: N v AST
freshVar =
  do s <- freshSymbol
     d <- gets domain
     z3 (mkVar s d)
     -- nb: could use mkFreshConst

name :: v -> N v AST
name x = gets ((M.! x) . names)

{-
name :: v -> N v AST
name a =
  do mn <- gets (M.lookup a . names)
     case mn of
       Just n  -> return n
       Nothing ->
         do x <- fresh
            n <- z3 $ mkIntSymbol x
            modM(names) (M.insert a n)
            return n
-}


eval :: Expr v -> N v (Object v)
eval e0 =
  case e0 of
    Var x -> name x

    Con k es -> cons k <$> mapM eval es

    App _ f es ->
      do as <- mapM eval es
         mr <- gets (M.lookup (f,as) . memo)
         ma <- gets (M.lookup f . apps)
         case (ma,mr) of
           (Just (xs,r,m),_) ->
             do zipWithM_ (equalASTHere . objectAst) as xs
                m
                return r

           (_,Just r) -> return r

           _ ->
             do modM(memo) (M.insert (f,as) (error "blackhole"))
                (xs,fe) <- gets ((M.! f) . funcs)
                localNames (M.union (M.fromList (xs `zip` as))) $
                  do r <- eval fe
                     modM(memo) (M.insert (f,as) r)
                     return r

    Later e ->
      do r <- freshVar
         enqueue (equalHere r =<< eval e)
         return r

    Let x xe e ->
      do v <- freshVar
         equalHere v =<< eval xe
         localNames (M.insert x v) (eval e)

    LetApp f xs fe e ->
      do as <- sequence [ (,) a <$> freshVar | a <- as ]
         r <- freshVar
         m <- runOnce (equalHere r =<< localNames (M.union (M.fromList as)) (eval fe))
         modM(apps) (M.insert f (map snd as,r,m))
         eval e

    Case e cs brs ->
      do s <- eval e
         mcls <- gets (M.lookup s splits)
         cls <-
           case mcls of
             Just cls -> do return cls
             Nothing  -> do ls <- lits (length cs)
                            let cls = [ (c,l)  | (Cons c _ _,l) <- cs `zip` ls ]
                            modM(splits) (M.insert s cls)
                            return cls
         r <- freshVar
         sequence_

--------------------------------------------------------------------------------
-- Objects

data Object v
  = Con AST (Thunk v (Val v,[Object v]))
  -- or int
  -- or bool
  -- h m m

newObject :: Bool -> Type v -> Object v
newObject inp (Type tc _args cs)

cmpView :: Object v -> AST
cmpView (Static a _ _)    = a
cmpView (Dynamic a _ _ _) = a

instance Eq a => Eq (Object a) where
  (==) = (==) `on` cmpView

instance Ord a => Ord (Object a) where
  compare = compare `on` cmpView

objectAst :: Object v -> AST
objectAst (Con a _ _) = a

cons :: v -> [Object v] -> Object v
cons cs@(Cons k _ _) os =
  do f <- sig k
     ast <- z3 (mkApp f (map objectAst os))
     return (Con ast c (map this os))

--------------------------------------------------------------------------------
-- Thunks

sig :: v -> N v FuncDecl
sig f = gets ((M.! f) . sigs)

newtype Unique = Unique Int deriving (Eq,Ord,Show)

freshUnique :: N v Unique
freshUnique = fmap Unique fresh

data Thunk v a
  = This a
  | Delay Bool Unique (IORef (Either (N v ()) a))
  | Inaccessible

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

this :: a -> Thunk v a
this x = This x

delay :: Bool -> N v a -> N v (Thunk v a)
delay inp m =
  do ref <- io $ newIORef undefined
     f <- saveLocals
     io $ writeIORef ref $ Left $
       do modify f
          x <- m
          io (writeIORef ref (Right x))
     unq <- freshUnique
     return (Delay inp unq ref)

inaccessible :: Thunk v a
inaccessible = Inaccessible

poke :: Thunk v a -> N v ()
poke (This _)        = do return ()
poke Inaccessible    = do assertHere =<< z3 mkFalse
poke (Delay _ _ ref) =
  do ema <- io $ readIORef ref
     case ema of
       Left m  -> m
       Right _ -> return ()

peek :: Thunk v a -> H v (Maybe a)
peek (This x)        = return (Just x)
peek Inaccessible    = return Nothing
peek (Delay _ _ ref) =
  do ema <- io $ readIORef ref
     return $ case ema of
       Left _  -> Nothing
       Right a -> Just a

force :: Thunk v a -> N v a
force th =
  do poke th
     ~(Just x) <- peek th
     return x

doForce :: Thunk v a -> (a -> N v ()) -> N v ()
doForce t h = force t >>= h

ifForce :: Thunk a -> (a -> N v ()) -> N v ()
ifForce (This x)               h = h x
ifForce Inaccessible           h = assertHere =<< z3 mkFalse
ifForce th@(Delay inp unq ref) h =
  do ema <- io $ readIORef ref
     case ema of
       Left m  ->
         do f <- saveLocals
            io $ writeIORef ref $ Left $
              do m
                 Just a <- peek th
                 modify f
                 h a
            if inp then
              enqueue (poke th)
             else
              return ()
       Right a -> h a

--------------------------------------------------------------------------------
-- Values

newtype Val a = Val [(AST,a)] -- sorted on a
 deriving ( Eq, Ord )

instance Show a => Show (Val a) where
  show (Val xs) = "[" ++ concat (intersperse "," [ show x | (_,x) <- xs ]) ++ "]"

val :: a -> Val a
val x = Val [(tt,x)]

(=?) :: Eq a => Val a -> a -> AST
Val []         =? x  = ff
Val ((a,y):xs) =? x
  | x == y      = a
  | otherwise   = Val xs =? x

domain :: Val a -> [a]
domain (Val xs) = map snd xs

newVal :: Ord a => [a] -> N v (Val a)
newVal xs =
  do as <- lits (length ys)
     return (Val (as `zip` ys))
  where
  ys = map head . group . sort $ xs

newBool :: N v AST
newBool = z3 . mkBoolVar =<< freshSymbol

lits :: Int -> N v [AST]
lits 1 = do z3 mkTrue
lits 2 = do a <- newBool
            nta <- z3 (mkNot a)
            return [a,nta]
lits n =
  do as <- sequence [ newBool | i <- [1..n] ]
     assert =<< z3 (mkOr as)
     atMostOne n =<< mapM (z3 . mkNot) as
     return as
  where

  atMostOne n as | n <= 5 =
    do sequence_ [ addClause [ntx, nty] | (ntx,nty) <- pairs as ]
   where
    pairs (x:xs) = [ (x,y) | y <- xs ] ++ pairs xs
    pairs _      = []

  atMostOne n as =
    do a <- newBit
       atMostOne (k+1) (a : take k as)
       atMostOne (n-k+1) (nt a : drop k as)
   where
    k = n `div` 2
