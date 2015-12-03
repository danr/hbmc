module Program where

import qualified Data.Map as M
import Data.Map( Map )
import Data.Maybe( fromJust )
import Data.List( intersperse )

import Object

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

unitT :: Type
unitT = Type "()" [] [unit]

unit :: Cons
unit = Cons "()" [] unitT

--------------------------------------------------------------------------------------------

eval :: Program -> Map Name (Object,[Object],Object) -> Map Name Object -> Expr -> M Object
eval prog apps env (Var x) =
  do return (fromJust (M.lookup x env))

eval prog apps env (Con c as) =
  do ys <- sequence [ eval prog apps env a | a <- as ]
     return (cons c ys)
     
eval prog apps env (App f as) =
  case (M.lookup f apps, M.lookup f prog) of
    (Just (trig,ys,z), _) ->
      do isCons trig unit $ \_ ->
           sequence_ [ evalInto prog apps env a y | (a,y) <- as `zipp` ys ]
         return z

    (_, Just (xs,rhs)) ->
      do ys <- sequence [ eval prog apps env a | a <- as ]
         eval prog M.empty (M.fromList (xs `zipp` ys)) rhs

eval prog apps env (Let x a b) =
  do y <- eval prog apps env a
     eval prog apps (M.insert x y env) b

eval prog apps env (LetApp f xs a b) =
  do trig <- new
     ys   <- sequence [ new | x <- xs ]
     z    <- new
     ifCons trig unit $ \_ ->
       evalInto prog apps (inserts (xs `zipp` ys) env) a z
     eval prog (M.insert f (trig,ys,z) apps) env b

eval prog apps env (Case a alts) =
  do res <- new
     evalInto prog apps env (Case a alts) res
     return res

--------------------------------------------------------------------------------------------

evalInto :: Program -> Map Name (Object,[Object],Object) -> Map Name Object -> Expr -> Object -> M ()
evalInto prog apps env (Var x) res =
  do fromJust (M.lookup x env) >>> res

evalInto prog apps env (Con c as) res =
  do isCons res c $ \ys ->
       sequence_ [ evalInto prog apps env a y | (a,y) <- as `zipp` ys ]

evalInto prog apps env (App f as) res =
  case (M.lookup f apps, M.lookup f prog) of
    (Just (trig,ys,z), _) ->
      do isCons trig unit $ \_ ->
           sequence_ [ evalInto prog apps env a y | (a,y) <- as `zipp` ys ]
         z >>> res

    (_, Just (xs,rhs)) ->
      do ys <- sequence [ eval prog apps env a | a <- as ]
         evalInto prog M.empty (M.fromList (xs `zipp` ys)) rhs res

evalInto prog apps env (Let x a b) res =
  do y <- eval prog apps env a
     evalInto prog apps (M.insert x y env) b res

evalInto prog apps env (LetApp f xs a b) res =
  do trig <- new
     ys   <- sequence [ new | x <- xs ]
     z    <- new
     ifCons trig unit $ \_ ->
       evalInto prog apps (inserts (xs `zipp` ys) env) a z
     evalInto prog (M.insert f (trig,ys,z) apps) env b res

evalInto prog apps env (Case a alts) res =
  do y <- eval prog apps env a
     sequence_
       [ ifCons y c $ \ys ->
           evalInto prog apps (inserts (xs `zipp` ys) env) rhs res
       | (c,xs,rhs) <- alts
       ]
  
--------------------------------------------------------------------------------------------

zipp :: [a] -> [b] -> [(a,b)]
zipp []     []     = []
zipp (x:xs) (y:ys) = (x,y) : zipp xs ys
zipp _      _      = error "zipp: unequal lengths"

inserts :: Ord a => [(a,b)] -> Map a b -> Map a b
inserts xys mp = foldr (\(x,y) -> M.insert x y) mp xys

--------------------------------------------------------------------------------------------


