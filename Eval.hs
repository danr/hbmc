module Main where

import Symbolic
import MiniSat
import H

import Data.List as L

import Control.Applicative

import Text.Show.Pretty (ppShow)

bruijn :: Integral i => i -> SymTerm
bruijn 0 = z
bruijn n = s (bruijn (n-1))

tnat = TApp "Nat" []
nat  = Data tnat [("Z",[]),("S",[tnat])]

texpr = TApp "Expr" []
expr  = Data texpr [ ("App2",[tnat,texpr,texpr])
                   , ("Case",[tnat,texpr,texpr])
                   , ("Cons",[texpr,texpr])
                   , ("Nil", [])
                   , ("Var", [tnat])
                   ]

z   = Con nat (val "Z") []
s x = Con nat (val "S") [(x,tnat)]

app2  f x y = Con expr (val "App2") [(f,tnat), (x,texpr), (y,texpr)]
ecase v x y = Con expr (val "Case") [(v,tnat), (x,texpr), (y,texpr)]
econs   x y = Con expr (val "Cons") [   (x,texpr), (y,texpr)]
enil        = Con expr (val "Nil")  [       ]
evar  v     = Con expr (val "Var")  [(v,tnat)      ]

type Expr = SymTerm

pprint :: Show a => a -> IO ()
pprint = putStrLn . ppShow

evalH :: List Expr -> List (List Nat) -> Expr -> H (List Nat)
evalH p env e = do
    io $ pprint ("evalH",e)
    (arg1,env1,arg2) <- match e
        [ ("Var",  \[v]     -> return (UNR,UNR,UNR))
        , ("App2", \[f,x,y] -> return (The x,The env,The y))
        , ("Case", \[v,n,c] -> do
            t <- index v env
            matchList True t
                (return (The n,The env,UNR))
                (\a as -> return (The c,The ((a `cons` Nil) `cons` (as `cons` env)),UNR))
          )
        , ("Cons", \[x,xs]  -> return (The x,The env,The xs))
        , ("Nil",  \[]      -> return (UNR,UNR,UNR))
        ]
    f1 <- lift (peek env1 >>= \e1 -> peek arg1 >>= \a1 -> evalH p e1 a1)
    f2 <- lift (peek arg2 >>= \a2 -> evalH p env a2)
    match e
        [ ("Var",  \[v]     -> do i <- index v env; return i)
        , ("App2", \[f,x,y] -> do check; evalH p (cons (the f1) (cons (the f2) Nil)) =<< index f p)
        , ("Case", \[v,n,c] -> return (the f1))
        , ("Cons", \[x,xs]  ->
            matchList False (the f1)
              (return (cons (fromInt 0) (the f2)))
              (\y _ -> return (cons y (the f2)))
          )
        , ("Nil",  \[]      -> return Nil)
        ]

eval :: Solver -> List Expr -> List (List Nat) -> Expr -> IO (List Nat)
eval s prog env e =
  do mx <- run (evalH prog env e) s []
     case mx of
       Just x -> return x
       Nothing -> error "eval = Nothing"

{-
  case e of
    Var v          -> index v env

    App2 f x y     -> let a = eval p env x
                          b = eval p env y
                       in eval p [a,b] (index f p)

    Case v nil cns -> case index v env of
                        []   -> eval p env nil
                        a:as -> eval p ([a]:as:env) cns

    Cons x xs      -> let a  = eval p env x
                          as = eval p env xs
                       in (case a of
                             []  -> 0
                             y:_ -> y) : as

    Nil            -> []
    -}

newProg :: Solver -> Int -> Int -> IO (List Expr)
newProg s fns e_size = fromList <$> sequence [ newTopExpr s f e_size | f <- [0..fns-1] ]

newTopExpr :: Solver -> Int -> Int -> IO Expr
newTopExpr s f size = do
    nil_e  <- newExpr s f Nothing                                                     2 (size-1)
    cons_e <- newExpr s f (Just (\ arg_e -> app2 (bruijn f) (evar (bruijn 1)) arg_e)) 4 (size-1)
    choices s [ nil_e , ecase (bruijn 0) nil_e cons_e ]

newExpr :: Solver -> Int -> Maybe (Expr -> Expr) -> Int -> Int -> IO Expr
newExpr s f rec vars size | size <= 0 = choices s (enil:map (evar . bruijn) [0..vars-1])
newExpr s f rec vars size = do

    e1 <- newExpr s f rec vars (size-1)
    e2 <- newExpr s f rec vars (size-1)
    v  <- choices s (map bruijn [0..vars-1])

    -- call earlier function on any argument
    mg <- if f > 0 then Just <$> choices s (map bruijn [0..f-1]) else return Nothing

    e <- choices s $
            [ app2 g e1 e2 | Just g <- [mg] ] ++
            [ econs e1 e2, evar v, enil ]

    case rec of
        Just k  -> choices s [ e , k e1 ] -- can call itself, e1 specifies second argument
                                          -- (first is tail from case)
        Nothing -> return e

index :: Symbolic a => SymTerm -> List a -> H a
index i xs =
  matchList False xs
    (impossible)
    (\y ys -> match i
              [ ("Z", \_   -> return y)
              , ("S", \[j] -> index j ys)
              ])

fromList :: Symbolic a => [a] -> List a
fromList = foldr cons Nil

fromIntList :: [Integer] -> List Nat
fromIntList = fromList . map fromInt

makeEnv :: [[Integer]] -> List (List Nat)
makeEnv = fromList . map fromIntList

main :: IO ()
main = do
    s <- newSolver
    eliminate s True

    putStrLn "Creating symbolic program..."

    let funs      = 1
        expr_size = 3

    prog <- newProg s funs expr_size

    pprint prog

    let test op a b =
          do r <- eval s prog (makeEnv [a,b])
                              (app2 (bruijn (funs-1)) (evar (bruijn 0)) (evar (bruijn 1)))
             pprint ("r",r)
             pprint ("op a b",fromIntList (op a b))
             eq <- equal s (fromIntList (op a b)) r
             addClauseBit s [eq]

    putStrLn "Adding tests..."

    test (\ xs ys -> xs ++ ys) [1,2] [4,5]
    -- test (\ xs ys -> xs ++ ys) [1,2,3] [4,5,6]
    -- test (\ xs ys -> reverse xs ++ ys) [1,2] [4,5]
    -- test (\ xs ys -> reverse xs ++ ys) [1,2,3] [4,5,6]
    -- test (\ xs ys -> reverse xs ++ ys) [1,2,3] []
    -- test (\ xs ys -> xs ++ xs) [1,2,3] []
    -- test (\ xs _ -> xs ++ xs) [1,2,3] []

    -- size=4, 0m23.256s: f1 = case a1 of { [] -> a2; x:y -> ((a1:[]):(x:f1(y,y))) }
    -- test (\ _ _ -> [1,1,2,2,3,3]) [1,2,3] []

    -- size=4, 0m0.435: sf1 = case a1 of { [] -> ([]:(a2:a1)); x:y -> ((a1:([]:[])):(x:(y:y))) }
    -- test (\ _ _ -> [1,1,2,2]) [1,2] []

    putStrLn "Solving..."
    b <- solve s []
    if b then
      do putStrLn "Solution!"
         pprint =<< get s prog
         pprint . map toExp =<< get s prog
         putStrLn . showProg . map toExp =<< get s prog
     else
      do putStrLn "No solution."

    deleteSolver s

--------------------------------------------------------------------------------

data Peano = Z | S Peano
 deriving ( Eq, Ord, Show )

data Exp
  = App Peano [Exp]
  | Case Peano Exp Exp
  | Cons Exp Exp
  | ENil
  | Var Peano
 deriving ( Eq, Ord, Show )

toExp :: Term -> Exp
toExp tm = case tm of
    Fun "App2" [f,x,y] -> App (toPeano f) [toExp x,toExp y]
    Fun "Case" [v,x,y] -> Case (toPeano v) (toExp x) (toExp y)
    Fun "Cons" [x,y]   -> Cons (toExp x) (toExp y)
    Fun "Nil"  []      -> ENil
    Fun "Var"  [v]     -> Var (toPeano v)
    _                  -> error $ "toExp: " ++ ppShow tm

toPeano :: Term -> Peano
toPeano tm = case tm of
    Fun "Z" []  -> Z
    Fun "S" [x] -> S (toPeano x)
    _           -> error $ "toPeano: " ++ ppShow tm

prog :: [Exp]
prog =
  [ App (S Z) [Var Z, ENil]
  , Case Z (Var (S Z)) (App (S Z) [Var (S Z), Cons (Var Z) (Var (S (S (S Z))))])
  ]

indexPeano :: Show a => Peano -> [a] -> a
indexPeano Z     (x:xs) = x
indexPeano (S n) (x:xs) = indexPeano n xs
indexPeano n     xs     = error $ "indexPeano: " ++ ppShow n ++ ", " ++ ppShow xs

showExp :: [String] -> [String] -> Exp -> String
showExp prg env (App f xs) =
  indexPeano f prg ++ "(" ++ concat (L.intersperse "," (map (showExp prg env) xs)) ++ ")"

showExp prg env (Case v nil cns) =
  "case " ++ indexPeano v env ++ " of { [] -> " ++ showExp prg env nil
          ++ "; " ++ x ++ ":" ++ xs ++ " -> " ++ showExp prg (x:xs:env) cns ++ " }"
 where
  x:xs:_ = new env

showExp prg env (Cons a as) =
  "(" ++ showExp prg env a ++ ":" ++ showExp prg env as ++ ")"

showExp prg env ENil =
  "[]"

showExp prg env (Var v) =
  indexPeano v env

new :: [String] -> [String]
new vs = (["x","y","z","v","w","p","q","r"] ++ ["x" ++ show i | i <- [1..] ]) L.\\ L.nub vs

showProg :: [Exp] -> String
showProg prg = unlines
  [ f ++ " = " ++ showExp fs env e
  | (f,e) <- fs `zip` prg
  ]
 where
  fs  = ["f" ++ show i | i <- [1..] ]
  env = ["a" ++ show i | i <- [1..10] ]

--------------------------------------------------------------------------------

{-


[ Fun
    "Case"
    [ Fun "Z" []
    , Fun "Var" [ Fun "S" [ Fun "Z" [] ] ]
    , Fun
        "App2"
        [ Fun "Z" []
        , Fun "Var" [ Fun "S" [ Fun "Z" [] ] ]
        , Fun
            "Cons"
            [ Fun "Var" [ Fun "S" [ Fun "Z" [] ] ]
            , Fun "Var" [ Fun "S" [ Fun "S" [ Fun "S" [ Fun "Z" [] ] ] ] ]
            ]
        ]
    ]
]
-}

{-
f xs ys = case xs of
    []   -> ys
    z:zs -> (z : xs) : f zs ys
-}
