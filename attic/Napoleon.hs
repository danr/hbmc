{-# LANGUAGE OverloadedStrings, TemplateHaskell, MultiParamTypeClasses #-}
module Main where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.RWS as RWS
import Data.IORef
import System.TimeIt
import Z3.Monad as Z3
import Text.PrettyPrint
import Data.Char (isDigit,chr)
import Data.Map (Map)
import Data.Generics.Geniplate
import qualified Data.Map as M
import System.IO
import Text.Printf

-- formulae --

data Form
    = Or [Form] | And [Form]
    | Form :<==>: Form | Form :==> Form
    | Not Form | Term :=: Term
    | Term Term -- lifting boolean terms into formulae

infixr 4 /\
infixr 3 \/
infixr 2 ==>
infix  1 <==>

(<==>),(==>) :: Form -> Form -> Form
(<==>) = (:<==>:)
(==>)  = (:==>)

(\/) :: Form -> Form -> Form
Or xs \/ Or ys = Or (xs ++ ys)
Or xs \/ y     = Or (xs ++ [y])
x     \/ Or ys = Or (x:ys)
x     \/ y     = Or [x,y]

(/\) :: Form -> Form -> Form
And xs /\ And ys = And (xs ++ ys)
And xs /\ y      = And (xs ++ [y])
x      /\ And ys = And (x:ys)
x      /\ y      = And [x,y]

data Term = String :$ [Term] | Lit Integer

instance Num Term where
    fromInteger = Lit
    x + y = "+" :$ [x,y]
    x - y = "-" :$ [x,y]
    x * y = "*" :$ [x,y]
    abs    = error "Term abs"
    signum = error "Term signum"

-- generics --

return []

instanceUniverseBi [t| (Form,Term) |]

congruences :: Form -> Form
congruences form = And
    [ x :=: hd ys /\ xs :=: tl ys
    | ys@("cons" :$ [x,xs]) <- universeBi form
    ]

-- interpreting --

type IVar = String -> Z3 FuncDecl

iForm :: IVar -> Form -> Z3 AST
iForm iVar f0 = case f0 of
    And []       -> mkTrue
    And fs       -> mkAnd =<< mapM go fs
    Or []        -> mkFalse
    Or fs        -> mkOr =<< mapM go fs
    f1 :==> f2   -> join $ mkImplies <$> go f1 <*> go f2
    f1 :<==>: f2 -> join $ mkEq <$> go f1 <*> go f2
    Not f        -> mkNot =<< go f
    t1 :=: t2    -> join $ mkEq <$> iTerm iVar t1 <*> iTerm iVar t2
    Term t       -> iTerm iVar t
  where
    go = iForm iVar

iTerm :: IVar -> Term -> Z3 AST
iTerm iVar tm0 = case tm0 of
    "<"  :$ ts -> bin mkLt ts
    "<=" :$ ts -> bin mkLe ts
    ">"  :$ ts -> bin mkGt ts
    "+"  :$ ts -> mkAdd =<< mapM go ts
    "-"  :$ ts -> mkSub =<< mapM go ts
    "*"  :$ ts -> mkMul =<< mapM go ts
    s :$ ts -> join $ mkApp <$> iVar s <*> mapM go ts
    Lit i   -> mkInt i
  where
    go = iTerm iVar

    bin mk [t1,t2] = join $ mk <$> go t1 <*> go t2

-- examples --

type Example = ([Term],Form)

app_len :: Integer -> Example
app_len size = runN size $ do
    let xs = var "xs"
    let ys = var "ys"
    res <- app_contract xs ys
    len_xs <- clen xs
    len_ys <- ulen ys
    len_res <- ulen res
    assert (Not (len_res :=: (len_xs + len_ys)))
    return [xs,ys]

reversing :: Integer -> Example
reversing size = runN (size + 1) $ do
    let xs = var "xs"
    equal xs =<< qrev xs nil
    le (Lit size) =<< len xs
    return [xs]

sort_inj :: (Term -> N Term) -> Integer -> Example
sort_inj sorter size = runN (size + 2) $ do
    let xs = var "xs"
    let ys = var "ys"
    join $ equal <$> sorter xs <*> sorter ys
    assert (Not (xs :=: ys))
    le (Lit size) =<< len xs
    le (Lit size) =<< len ys
    return [xs,ys]

sort_triple :: (Term -> N Term) -> Integer -> Example
sort_triple sorter size = runN (size + 2) $ do
    let xs = var "xs"
    let ys = var "ys"
    sort_xs <- sorter xs
    sort_ys <- sorter ys
    le (Lit size) =<< len xs
    le (Lit size) =<< len ys
    assert $ Not $
           sort_xs :=: sort_ys
       ==> xs :=: ys
        \/ sort_xs :=: xs
        \/ sort_ys :=: ys
    return [xs,ys]

commutative :: (Term -> Term -> N Term) -> Integer -> Example
commutative f size = runN (size + 1) $ do
    let xs = var "xs"
    let ys = var "ys"
    xy <- f xs ys
    yx <- f ys xs
    assert (Not (xy :=: yx))
    le (Lit size) =<< len xs
    le (Lit size) =<< len ys
    return [xs,ys]

-- main --

main :: IO ()
main = do
    runExample (app_len 1)

bla =
    sequence_
        [ timeIt $ do
            printf "%02d: " i
            runExample (sort_triple isort i)
        | i <- [0..]
        ]

-- run --

runExample :: Example -> IO ()
runExample (vars,form) = evalZ3 $ do

    int <- mkIntSort
    bool <- mkBoolSort
    list <- mkUninterpretedSort =<< mkStringSymbol "List"

    let func name args res = do
            symbol <- mkStringSymbol name
            decl <- mkFuncDecl symbol args res
            return (name,decl)

    env_ref <- liftIO . newIORef . M.fromList =<< sequence
        ([ func v [] list | v :$ [] <- vars ] ++
         [ func "len" [list] int
         , func "app" [list,list] list
         , func "qrev" [list,list] list
         , func "ins" [int,list] list
         , func "isort" [list] list
         , func "msort" [list] list
         , func "rev" [list] list
         , func "cons" [int,list] list
         , func "head" [list] int
         , func "tail" [list] list
         , func "merge" [list,list] list
         , func "evens" [list] list
         , func "odds" [list] list
         , func "nil" [] list
         ])

    let insert (s,fd) = do
            liftIO (modifyIORef env_ref (M.insert s fd))
            return fd

        iVar s = do
            env <- liftIO $ readIORef env_ref
            case M.lookup s env of
                Just fd -> return fd
                Nothing -> case s of
                    'b':i | all isDigit i -> insert =<< func s [] bool
                    'r':i | all isDigit i -> insert =<< func s [] int
                    'l':i | all isDigit i -> insert =<< func s [] list
                    _     -> error $ "Undeclared function: " ++ s

    let get_list m t = do
            is_nil <- Z3.local $ do
                assertCnstr =<< iForm iVar ((t :=: nil))
                (Sat ==) <$> check
            if is_nil then
                return []
            else do
                -- Just tast <- eval m =<< iTerm iVar t
                -- liftIO . putStrLn . ("not nil: " ++) =<< astToString tast
                Just xx <- eval m =<< iTerm iVar (hd t)
                -- s <- astToString xx
                x <- getInt xx
                xs <- get_list m (tl t)
                return (x:xs)

    let cong = congruences form

    liftIO $ putStrLn (render (ppForm form))
    -- liftIO $ putStrLn (render (ppForm cong))

    liftIO $ putStr "adding assertions... " >> hFlush stdout
    assertCnstr =<< iForm iVar (form /\ cong)

    liftIO $ putStr "solving... " >> hFlush stdout
    (res,mm) <- getModel

    liftIO $ print res

    case mm of
        Just m  -> do
            liftIO . putStrLn =<< showModel m
            forM_ vars $ \ v -> liftIO . print =<< get_list m v
            return ()
        Nothing -> return ()

-- Napoleon monad --

type N = RWS (Form,Integer) [Form] Int

runN :: Integer -> N a -> (a,Form)
runN fuel m =
    let (a,axs) = evalRWS m (And [],fuel) 0
    in  (a,And axs)

assert :: Form -> N ()
assert form = do
    (ctx,_) <- ask
    tell [ctx ==> form]

fresh :: N Int
fresh = state $ \ i -> (i,i+1)

newVar :: String -> N Term
newVar s = do
    i <- fresh
    return (var (s ++ show i))

withContext :: Form -> N a -> N a
withContext phi = RWS.local $ \ (ctx,fuel) -> (phi /\ ctx,fuel)

-- utilities --

impossible :: N ()
impossible = assert (Or [])

le :: Term -> Term -> N ()
le a b = assert (a .<=. b)

equal :: Term -> Term -> N ()
equal a b = assert (a :=: b)

-- term builders --

var :: String -> Term
var x = x :$ []

(.<.) :: Term -> Term -> Form
x .<. y = Term ("<" :$ [x,y])

(.<=.) :: Term -> Term -> Form
x .<=. y = Term ("<=" :$ [x,y])

(.>.) :: Term -> Term -> Form
x .>. y = Term (">" :$ [x,y])

tl :: Term -> Term
tl xs = "tail" :$ [xs]

hd :: Term -> Term
hd xs = "head" :$ [xs]

cons :: Term -> Term -> Term
cons x xs = "cons" :$ [x,xs]

nil :: Term
nil = "nil" :$ []

-- functions --

listCase :: Term -> N () -> (Term -> Term -> N ()) -> N ()
listCase xs mk_nil mk_cons = do
    b <- Term <$> newVar "b"
    assert (b     <==> xs :=: nil)
    assert (Not b <==> xs :=: cons (hd xs) (tl xs))
    withContext b       mk_nil
    withContext (Not b) (mk_cons (hd xs) (tl xs))

listCase' :: Term -> N Term -> (Term -> Term -> N Term) -> Term -> N ()
listCase' xs mk_nil mk_cons res = listCase xs
    (mk_nil >>= \ tm -> equal res tm)
    (\ h t -> mk_cons h t >>= \ tm -> equal res tm)

define' :: Bool -> Term -> String -> (Term -> N ()) -> N Term
define' b tm r k = do
    (ctx,fuel) <- ask
    if fuel <= 0
        then if b then impossible else return ()
        else do
            RWS.local (const (ctx,fuel-1)) $ do
                res <- newVar r
                equal tm res
                k res
    return tm

define :: Term -> String -> (Term -> N ()) -> N Term
define = define' True

len' :: Bool -> Term -> N Term
len' b xs =
    define' b ("len" :$ [xs]) "r" $ listCase' xs
        (return 0)
        (\ _ t -> (1 +) <$> len' b t)

len :: Term -> N Term
len = len' True

clen :: Term -> N Term
clen x = len' False x

ulen :: Term -> N Term
ulen x = return ("len" :$ [x])

app :: Term -> Term -> N Term
app xs ys =
    define ("app" :$ [xs,ys]) "l" $ listCase' xs
        (return ys)
        (\ h t -> cons h <$> app t ys)

app_contract :: Term -> Term -> N Term
app_contract xs ys =
    define' False ("app" :$ [xs,ys]) "l" $ listCase' xs
        (return ys)
        (\ h t -> do
            res <- cons h <$> app_contract t ys
            len_xs  <- ulen xs
            len_ys  <- ulen ys
            len_res <- ulen res
            assert (len_res :=: (len_xs + len_ys))
            return res)

rev :: Term -> N Term
rev xs =
    define ("rev" :$ [xs]) "l" $ listCase' xs
        (return nil)
        (\ h t -> do
            r <- rev t
            app r (cons h nil))

qrev :: Term -> Term -> N Term
qrev xs ys =
    define ("qrev" :$ [xs,ys]) "l" $ listCase' xs
        (return ys)
        (\ h t -> do
            qrev t (cons h ys))


ins :: Term -> Term -> N Term
ins x xs = do
    define ("ins" :$ [x,xs]) "l" $ \ res -> listCase xs
        (equal res (cons x nil))
        (\ h t -> do
            withContext (x .<. h) (equal res (cons x xs))
            withContext (Not (x .<. h)) $ do
                tl <- ins x t
                equal res (cons h tl))

isort :: Term -> N Term
isort xs = do
    define ("isort" :$ [xs]) "l" $ listCase' xs
        (return nil)
        (\ h t -> ins h =<< isort t)

merge :: Term -> Term -> N Term
merge xs ys =
    define ("merge" :$ [xs,ys]) "l" $ \ res -> listCase xs
        (equal res ys)
        (\ x xs_tail -> listCase ys
            (equal res xs)
            (\ y ys_tail -> do
                l1  <- newVar "l"
                l2  <- newVar "l"
                rec <- merge l1 l2
                withContext (x .<. y)       (assert $ l1 :=: xs_tail /\ l2 :=: ys /\ res :=: cons x rec)
                withContext (Not (x .<. y)) (assert $ l1 :=: xs /\ l2 :=: ys_tail /\ res :=: cons y rec)))

merge_slow :: Term -> Term -> N Term
merge_slow xs ys =
    define ("merge" :$ [xs,ys]) "l" $ \ res -> listCase xs
        (equal res ys)
        (\ x xs_tail -> listCase ys
            (equal res xs)
            (\ y ys_tail -> do
                withContext (x .<. y)       $ do equal res . cons x =<< merge_slow xs_tail ys
                withContext (Not (x .<. y)) $ do equal res . cons y =<< merge_slow xs ys_tail))

evens :: Term -> N Term
evens xs =
    define ("evens" :$ [xs]) "l" $ listCase' xs
        (return nil)
        (\ h t -> cons h <$> odds t)

odds :: Term -> N Term
odds xs =
    define ("odds" :$ [xs]) "l" $ listCase' xs
        (return nil)
        (\ _ t -> evens t)

msort :: Term -> N Term
msort xs =
    define ("msort" :$ [xs]) "l" $ \ res -> listCase xs
        (equal res xs)
        (\ x xs_tail -> listCase xs_tail
            (equal res xs)
            (\ y ys_tail -> do
                l1 <- msort =<< evens xs
                l2 <- msort =<< odds xs
                equal res =<< merge l1 l2))

msort_slow :: Term -> N Term
msort_slow xs =
    define ("msort" :$ [xs]) "l" $ \ res -> listCase xs
        (equal res xs)
        (\ x xs_tail -> listCase xs_tail
            (equal res xs)
            (\ y ys_tail -> do
                l1 <- msort_slow =<< evens xs
                l2 <- msort_slow =<< odds xs
                equal res =<< merge_slow l1 l2))


-- pretty printing --

infixr 1 $\

($\) :: Doc -> Doc -> Doc
d1 $\ d2 = hang d1 2 d2

ppForm :: Form -> Doc
ppForm f0 = case f0 of
    Or  []       -> "false"
    Or  fs       -> parens ("or" $\ sep (map ppForm fs))
    And []       -> "true"
    And fs       -> parens ("and" $\ sep (map ppForm fs))
    Not f        -> parens ("not" $\ ppForm f)
    t1 :=: t2    -> parens ("=" $\ sep (map ppTerm [t1,t2]))
    f1 :<==>: f2 -> parens ("<=>" $\ sep (map ppForm [f1,f2]))
    f1 :==> f2   -> parens ("=>" $\ sep (map ppForm [f1,f2]))
    Term t       -> ppTerm t

ppTerm :: Term -> Doc
ppTerm tm0 = case tm0 of
    f :$ [] -> text f
    f :$ ts -> parens (text f $\ sep (map ppTerm ts))
    Lit i   -> integer i

