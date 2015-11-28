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


