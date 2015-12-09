module HBMC.Program where

import qualified Data.Map as M
import Data.Map( Map )
import Data.Maybe( fromJust )
import Data.List( intersperse )

import HBMC.Object

--------------------------------------------------------------------------------------------

data Expr a
  = Var a
  | Con (Cons a) [Expr a]
  | App a [Expr a]
  | Later (Expr a)
  | Let a (Expr a) (Expr a)
  | LetApp a [a] (Expr a) (Expr a)
  | Case (Expr a) [(Cons a,[a],Expr a)]
 deriving ( Eq, Ord, Show )

type Program n = Map n ([n],Expr n)

type Apps n = Map n (Object n,[Object n],Object n)

type VarEnv n = Map n (Object n)

--------------------------------------------------------------------------------------------

eval :: (Names n,Ord n,Show n) => Program n -> Apps n -> VarEnv n -> Expr n -> M n (Object n)
eval prog apps env (Var x) =
  do return (fromJust (M.lookup x env))

eval prog apps env (Con c as) =
  do ys <- sequence [ eval prog apps env a | a <- as ]
     return (cons c ys)

eval prog apps env (App f as) =
  case (M.lookup f apps, M.lookup f prog) of
    (Just (trig,ys,z), _) ->
      do isCons trig true $ \_ ->
           sequence_ [ evalInto prog apps env a y | (a,y) <- zipp ("App/LetApp:" ++ show f) as ys ]
         return z

    (_, Just (xs,rhs)) ->
      do --liftIO $ putStrLn (show f ++ show as)
         ys <- sequence [ eval prog apps env a | a <- as ]
         eval prog M.empty (M.fromList (zipp ("App:" ++ show f) xs ys)) rhs

eval prog apps env (Later a) =
  do y <- new
     evalInto prog apps env (Later a) y
     return y

eval prog apps env (Let x a b) =
  do y <- eval prog apps env a
     eval prog apps (M.insert x y env) b

eval prog apps env (LetApp f xs a b) =
  do trig <- new
     ys   <- sequence [ new | x <- xs ]
     z    <- new
     ifCons trig true $ \_ ->
       evalInto prog apps (inserts (zipp ("LetApp:" ++ show f) xs ys) env) a z
     eval prog (M.insert f (trig,ys,z) apps) env b

eval prog apps env (Case a alts) =
  do res <- new
     evalInto prog apps env (Case a alts) res
     return res

--------------------------------------------------------------------------------------------

evalInto :: (Names n,Ord n,Show n) => Program n -> Apps n -> VarEnv n -> Expr n -> Object n -> M n ()
evalInto prog apps env (Var x) res =
  do fromJust (M.lookup x env) >>> res

evalInto prog apps env (Con c as) res =
  do isCons res c $ \ys ->
       sequence_ [ evalInto prog apps env a y | (a,y) <- zipp ("Con:" ++ show c ++ "->") as ys ]

evalInto prog apps env (App f as) res =
  case (M.lookup f apps, M.lookup f prog) of
    (Just (trig,ys,z), _) ->
      do isCons trig true $ \_ ->
           sequence_ [ evalInto prog apps env a y | (a,y) <- zipp ("App/LetApp:" ++ show f ++ "->") as ys ]
         z >>> res

    (_, Just (xs,rhs)) ->
      do --liftIO $ putStrLn (show f ++ show as)
         ys <- sequence [ eval prog apps env a | a <- as ]
         evalInto prog M.empty (M.fromList (zipp ("App:" ++ show f ++ "->") xs ys)) rhs res

evalInto prog apps env (Later a) res =
  do later (evalInto prog apps env (Later a) res)

evalInto prog apps env (Let x a b) res =
  do y <- eval prog apps env a
     evalInto prog apps (M.insert x y env) b res

evalInto prog apps env (LetApp f xs a b) res =
  do trig <- new
     ys   <- sequence [ new | x <- xs ]
     z    <- new
     ifCons trig true $ \_ ->
       evalInto prog apps (inserts (zipp ("LetApp:" ++ show f ++ "->") xs ys) env) a z
     evalInto prog (M.insert f (trig,ys,z) apps) env b res

evalInto prog apps env (Case a alts) res =
  do y <- eval prog apps env a
     sequence_
       [ ifCons y c $ \ys ->
           evalInto prog apps (inserts (zipp ("Case:" ++ show c) xs ys) env) rhs res
       | (c,xs,rhs) <- alts
       ]

--------------------------------------------------------------------------------------------

zipp :: String -> [a] -> [b] -> [(a,b)]
zipp s []     []     = []
zipp s (x:xs) (y:ys) = (x,y) : zipp s xs ys
zipp s _      _      = error ("zipp (" ++ s ++ "): unequal lengths")

inserts :: Ord a => [(a,b)] -> Map a b -> Map a b
inserts xys mp = foldr (\(x,y) -> M.insert x y) mp xys

--------------------------------------------------------------------------------------------


