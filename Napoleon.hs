{-# LANGUAGE OverloadedStrings, TypeSynonymInstances, FlexibleInstances #-}
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

reversing :: Integer -> Example
reversing size = runU $ do
    let xs = var "xs"
    len_axioms <- genLen [] (fuel (size + 5)) xs
    rev_axioms <- genRev [] (fuel (size + 5)) xs
    return
        ( [xs]
        , And
            [ len_axioms
            , rev_axioms
            , len xs .>. Lit size
            , xs :=: rev xs
            ]
        )

main :: IO ()
main = runExample (reversing 22)

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
         , func "eq" [list,list] bool
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
                assertCnstr =<< iForm iVar (t :=: nil)
                (Sat ==) <$> check
            if is_nil then
                return []
            else do
                -- Just tast <- eval m =<< iTerm iVar t
                -- liftIO . putStrLn . ("not nil: " ++) =<< astToString tast
                Just xx <- eval m =<< iTerm iVar (hd t)
                s <- astToString xx
                x <- getInt xx
                xs <- get_list m (tl t)
                return (chr (fromInteger x):xs)

    -- liftIO $ putStrLn (render (ppForm form))

    assertCnstr =<< iForm iVar form

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

eq :: Term -> Term -> Term
eq xs ys = "eq" :$ [xs,ys]

rev :: Term -> Term
rev xs = "rev" :$ [xs]

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
genLen ctx Z     xs = return (impossible ctx)
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

isCons :: Term -> (Term,Term) -> Form
ys `isCons` (x,xs) = And [ys :=: cons x xs,hd ys :=: x,tl ys :=: xs]

eqList :: Term -> Term -> Form
xs `eqList` ys = And [xs :=: ys,hd xs :=: hd ys,tl xs :=: tl ys]

genApp :: [Form] -> Fuel -> Term -> Term -> U Form
genApp ctx Z     xs ys = return (impossible ctx)
genApp ctx (S n) xs ys = do
    b   <- Term <$> newVar "b"
    res <- newVar "l"
    rec <- genApp (Not b:ctx) n (tl xs) ys
    return $ And
        [ app xs ys :=: res
        , b     <==> xs :=: nil
        , Not b <==> xs :=: cons (hd xs) (tl xs)
        , b     ==> res :=: ys
        , Not b ==> res `isCons` (hd xs,app (tl xs) ys)
        , rec
        ]

{-
genEq :: [Form] -> Fuel -> Term -> Term -> U Form
genEq ctx Z     xs ys = return (impossible ctx)
genEq ctx (S n) xs ys = do
    b   <- Term <$> newVar "b"
    c   <- Term <$> newVar "b"
    res <- newVar "b"
    rec <- genEq (Not b:Not c:ctx) n (tl xs) (tl ys)
    return $ And
        [ eq xs ys :=: res
        , b     <==> xs :=: nil
        , Not b <==> xs :=: cons (hd xs) (tl xs)
        , c     <==> ys :=: nil
        , Not c <==> ys :=: cons (hd ys) (tl ys)
        , b /\ c ==> res :=: tt
        , Not b /\ c ==> res :=: ff
        , b /\ Not c ==> res :=: ff
        , Not b /\ Not c /\ Not (hd xs :=: hd ys) ==> res :=: ff
        , Not b /\ Not c /\ hd xs :=: hd ys ==> res :=: eq (tl xs) (tl ys)
        , rec
        ]
-}

genRev :: [Form] -> Fuel -> Term -> U Form
genRev ctx Z     xs = return (impossible ctx)
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
        , Not b ==> res `eqList` app (rev (tl xs)) (cons (hd xs) nil)
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

