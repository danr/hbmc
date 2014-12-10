{-# LANGUAGE OverloadedStrings, TemplateHaskell, MultiParamTypeClasses #-}
module Main where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.State
import Data.IORef
import System.TimeIt
import Z3.Monad
import Text.PrettyPrint
import Data.Char (isDigit,chr)
import Data.Map (Map)
import Data.Generics.Geniplate
import qualified Data.Map as M

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
    And fs       -> mkAnd =<< mapM go fs
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
    "tt" :$ [] -> mkTrue
    "ff" :$ [] -> mkFalse
    "<" :$ ts -> bin mkLt ts
    ">" :$ ts -> bin mkGt ts
    "+" :$ ts -> mkAdd =<< mapM go ts
    "-" :$ ts -> mkSub =<< mapM go ts
    "*" :$ ts -> mkMul =<< mapM go ts
    s :$ ts -> join $ mkApp <$> iVar s <*> mapM go ts
    Lit i   -> mkInt i
  where
    go = iTerm iVar

    bin mk [t1,t2] = join $ mk <$> go t1 <*> go t2

-- main --

type Example = ([Term],Form)

mkRev :: Integer -> Term -> U (Term,Form)
mkRev i xs = (,) (rev xs) <$> genRev [] (fuel i) xs

mkLen :: Integer -> Term -> U (Term,Form)
mkLen i xs = (,) (len xs) <$> genLen [] (fuel i) xs

mkISort :: Integer -> Term -> U (Term,Form)
mkISort i xs = (,) (isort xs) <$> genISort [] (fuel i) xs

reversing :: Integer -> Example
reversing size = runU $ do
    let xs = var "xs"
    (len_xs,len_ax) <- mkLen (size + 2) xs
    (rev_xs,rev_ax) <- mkRev (size + 2) xs
    return
        ( [xs]
        , And
            [ len_ax
            , rev_ax
            , len_xs .>. Lit size
            , xs :=: rev_xs
            ]
        )

sort_inj :: Integer -> Example
sort_inj size = runU $ do
    let xs = var "xs"
    let ys = var "ys"
    (sort_xs,ax1) <- mkISort (size + 2) xs
    (sort_ys,ax2) <- mkISort (size + 2) ys
    (len_xs,ax3) <- mkLen (size + 2) xs
    (len_ys,ax4) <- mkLen (size + 2) ys
    return
        ( [xs,ys]
        , And
            [ ax1, ax2, ax3, ax4
            , sort_xs :=: sort_ys
            , Not (xs :=: ys)
            , len_xs .>. Lit size
            , len_ys .>. Lit size
            ]
        )

sort_triple :: Integer -> Example
sort_triple size = runU $ do
    let xs = var "xs"
    let ys = var "ys"
    let ys = var "zs"
    (sort_xs,ax1) <- mkISort (size + 2) xs
    (sort_ys,ax2) <- mkISort (size + 2) ys
    (len_xs,ax3) <- mkLen (size + 2) xs
    (len_ys,ax4) <- mkLen (size + 2) ys
    return
        ( [xs,ys]
        , And
            [ ax1, ax2, ax3, ax4
            , Not $ sort_xs :=: sort_ys
                ==> xs :=: ys
                 \/ sort_xs :=: xs
                 \/ sort_ys :=: ys
            , len_xs .>. Lit size
            , len_ys .>. Lit size
            ]
        )

sort_test :: Example
sort_test = runU $ do
    let mk_list = foldr cons nil
    let xs = var "xs"
    let ys = var "ys"
    sort_ax <- genISort [] (fuel 5) xs
    return
        ( [xs,ys]
        , And
            [ xs :=: mk_list [40,50,20,30]
            , sort_ax
            , isort xs :=: ys
            ]
        )

main :: IO ()
main = sequence_
    [ timeIt $ do
        print i
        runExample (sort_triple i)
    | i <- [0..]
    ]

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
         [ func "length" [list] int
         , func "app" [list,list] list
         , func "ins" [int,list] list
         , func "isort" [list] list
         , func "rev" [list] list
         , func "cons" [int,list] list
         , func "head" [list] int
         , func "tail" [list] list
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
            is_nil <- local $ do
                assertCnstr =<< iForm iVar (Not (t :=: nil))
                (Unsat ==) <$> check
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

    -- liftIO $ putStrLn (render (ppForm form))
    -- liftIO $ putStrLn (render (ppForm cong))

    assertCnstr =<< iForm iVar (form /\ cong)

    (res,mm) <- getModel

    liftIO $ print res

    case mm of
        Just m  -> do
            -- liftIO . putStrLn =<< showModel m
            forM_ vars $ \ v -> liftIO . print =<< get_list m v
        Nothing -> return ()

-- fuel  --

data Fuel = S Fuel | Z

fuel :: Integer -> Fuel
fuel i = iterate S Z !! fromInteger i

-- unique variable names --

type U a = State Int a

runU :: U a -> a
runU m = evalState m 0

fresh :: U Int
fresh = state $ \ i -> (i,i+1)

newVar :: String -> U Term
newVar s = do
    i <- fresh
    return (var (s ++ show i))

-- term builders --

var :: String -> Term
var x = x :$ []

(.<.) :: Term -> Term -> Form
x .<. y = Term ("<" :$ [x,y])

(.>.) :: Term -> Term -> Form
x .>. y = Term (">" :$ [x,y])

tl :: Term -> Term
tl xs = "tail" :$ [xs]

hd :: Term -> Term
hd xs = "head" :$ [xs]

cons :: Term -> Term -> Term
cons x xs = "cons" :$ [x,xs]

len :: Term -> Term
len xs = "length" :$ [xs]

app :: Term -> Term -> Term
app xs ys = "app" :$ [xs,ys]

rev :: Term -> Term
rev xs = "rev" :$ [xs]

ins :: Term -> Term -> Term
ins x xs = "ins" :$ [x,xs]

isort :: Term -> Term
isort xs = "isort" :$ [xs]

nil :: Term
nil = "nil" :$ []

tt :: Term
tt = "tt" :$ []

ff :: Term
ff = "ff" :$ []

-- impossible --

impossible :: [Form] -> Form
impossible ts = Not (And ts)

-- functions --

genLen :: [Form] -> Fuel -> Term -> U Form
genLen ctx Z     _  = return (impossible ctx)
genLen ctx (S n) xs = do
    b   <- Term <$> newVar "b"
    res <- newVar "r"
    rec <- genLen (Not b:ctx) n (tl xs)
    return $ And
        [ len xs :=: res
        , b     <==> xs :=: nil
        , Not b <==> xs :=: cons (hd xs) (tl xs)
        , b ==> res :=: 0
        , Not b ==> res :=: (1 + len (tl xs))
        , rec
        ]

genApp :: [Form] -> Fuel -> Term -> Term -> U Form
genApp ctx Z     _  _  = return (impossible ctx)
genApp ctx (S n) xs ys = do
    b   <- Term <$> newVar "b"
    res <- newVar "l"
    rec <- genApp (Not b:ctx) n (tl xs) ys
    return $ And
        [ app xs ys :=: res
        , b     <==> xs :=: nil
        , Not b <==> xs :=: cons (hd xs) (tl xs)
        , b     ==> res :=: ys
        , Not b ==> res :=: cons (hd xs) (app (tl xs) ys)
        , rec
        ]

genRev :: [Form] -> Fuel -> Term -> U Form
genRev ctx Z     _  = return (impossible ctx)
genRev ctx (S n) xs = do
    b   <- Term <$> newVar "b"
    res <- newVar "l"
    rec1 <- genRev (Not b:ctx) n (tl xs)
    rec2 <- genApp (Not b:ctx) n (rev (tl xs)) (cons (hd xs) nil)
    return $ And
        [ rev xs :=: res
        , b     <==> xs :=: nil
        , Not b <==> xs :=: cons (hd xs) (tl xs)
        , b ==> res :=: nil
        , Not b ==> res :=: app (rev (tl xs)) (cons (hd xs) nil)
        , rec1
        , rec2
        ]

genIns :: [Form] -> Fuel -> Term -> Term -> U Form
genIns ctx Z     _ _  = return (impossible ctx)
genIns ctx (S n) x xs = do
    b   <- Term <$> newVar "b"
    res <- newVar "l"
    rec <- genIns (Not b:ctx) n x (tl xs)
    return $ And
        [ ins x xs :=: res
        , b     <==> xs :=: nil
        , Not b <==> xs :=: cons (hd xs) (tl xs)
        , b ==> res :=: cons x nil
        , Not b /\ x .<. hd xs       ==> res :=: cons x (xs)
        , Not b /\ Not (x .<. hd xs) ==> res :=: cons (hd xs) (ins x (tl xs))
        , rec
        ]

genISort :: [Form] -> Fuel -> Term -> U Form
genISort ctx Z     _  = return (impossible ctx)
genISort ctx (S n) xs = do
    b   <- Term <$> newVar "b"
    res <- newVar "l"
    rec1 <- genISort (Not b:ctx) n (tl xs)
    rec2 <- genIns (Not b:ctx) n (hd xs) (isort (tl xs))
    return $ And
        [ isort xs :=: res
        , b     <==> xs :=: nil
        , Not b <==> xs :=: cons (hd xs) (tl xs)
        , b     ==> res :=: nil
        , Not b ==> res :=: ins (hd xs) (isort (tl xs))
        , rec1
        , rec2
        ]

-- pretty printing --

infixr 1 $\

($\) :: Doc -> Doc -> Doc
d1 $\ d2 = hang d1 2 d2

ppForm :: Form -> Doc
ppForm f0 = case f0 of
    Or  fs       -> parens ("or" $\ sep (map ppForm fs))
    And fs       -> parens ("and" $\ sep (map ppForm fs))
    Not f        -> parens ("not" $\ ppForm f)
    t1 :=: t2    -> parens ("=" $\ sep (map ppTerm [t1,t2]))
    f1 :<==>: f2 -> parens ("=" $\ sep (map ppForm [f1,f2]))
    f1 :==> f2   -> parens ("=>" $\ sep (map ppForm [f1,f2]))
    Term t       -> ppTerm t

ppTerm :: Term -> Doc
ppTerm tm0 = case tm0 of
    f :$ [] -> text f
    f :$ ts -> parens (text f $\ sep (map ppTerm ts))
    Lit i   -> integer i

