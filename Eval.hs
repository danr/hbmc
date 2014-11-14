module Main where

import Symbolic
import MiniSat
import H

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
    -- io $ pprint ("evalH",e)
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
        Just k  -> choices s [ e , k e2 ] -- can call itself, e2 specifies second argument
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
    prog <- newProg s 1 3

    pprint prog

    -- prog <- return Nil -- (cons enil (cons enil Nil))

    let test op a b =
          do r <- eval s prog (makeEnv [a,b]) -- (evar (bruijn 0))
                              (app2 (bruijn 0) (evar (bruijn 0)) (evar (bruijn 1)))
             pprint ("r",r)
             pprint ("op a b",fromIntList (op a b))
             eq <- equal s (fromIntList (op a b)) r
             addClauseBit s [eq]

    putStrLn "Adding tests..."
    test (++) [6,3,5] [2,8,4]

    putStrLn "Solving..."
    b <- solve s []
    if b then
      do putStrLn "Solution!"
         pprint =<< get s prog
     else
      do putStrLn "No solution."

    deleteSolver s

{-
prog =
  [ App (S Z) [Var Z, Nil]
  , Case Z (Var (S Z)) (App (S Z) [Var (S Z), Cons (Var Z) (Var (S (S (S Z))))])
  ]
-}

{-
data Expr
  = App Int [Expr]
  | Case Int Expr Expr
  | Cons Expr Expr
  | Nil
  | Var Int
 deriving ( Eq, Ord, Show )

showExpr :: [String] -> [String] -> Expr -> String
showExpr prg env (App f xs) =
  index f prg ++ "(" ++ concat (L.intersperse "," (map (showExpr prg env) xs)) ++ ")"

showExpr prg env (Case v nil cns) =
  "case " ++ index v env ++ " of { [] -> " ++ showExpr prg env nil
          ++ "; " ++ x ++ ":" ++ xs ++ " -> " ++ showExpr prg (x:xs:env) cns ++ " }"
 where
  x:xs:_ = new env

showExpr prg env (Cons a as) =
  "(" ++ showExpr prg env a ++ ":" ++ showExpr prg env as ++ ")"

showExpr prg env Nil =
  "[]"

showExpr prg env (Var v) =
  index v env

new :: [String] -> [String]
new vs = (["x","y","z","v","w","p","q","r"] ++ ["x" ++ show i | i <- [1..] ]) L.\\ L.nub vs

showProg :: Program -> String
showProg prg = unlines
  [ f ++ " = " ++ showExpr fs env e
  | (f,e) <- fs `zip` prg
  ]
 where
  fs  = ["f" ++ show i | i <- [1..] ]
  env = ["a" ++ show i | i <- [1..10] ]

-}

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
