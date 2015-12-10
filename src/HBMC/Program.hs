{-# LANGUAGE DeriveFunctor #-}
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
  | Case (Expr a) [(Maybe (Cons a),[a],Expr a)]

  | Proj (Expr a) (Type a) Int
  | ConstraintsOf [Expr a]
  | EqPrim EqPrim (Expr a) (Expr a)
 deriving ( Eq, Ord, Show, Functor )

noop :: Expr a
noop = ConstraintsOf []

data EqPrim = EqualHere | NotEqualHere
 deriving ( Eq, Ord, Show )

data MemoFlag = DoMemo | Don'tMemo
 deriving ( Eq, Ord, Show )

ifMemo :: Ord a => MemoFlag -> a -> ([Object a] -> M a [Object a]) -> [Object a] -> M a [Object a]
ifMemo DoMemo    = memo
ifMemo Don'tMemo = don'tMemo

type PreFunction n = (n,([n],MemoFlag,Expr n))

type Program n = Map n ([n],MemoFlag,Expr n)

type Apps n = Map n (Object n,[Object n],Object n)

type VarEnv n = Map n (Object n)

evalPrim :: (Names n,Ord n) => EqPrim -> Object n -> Object n -> M n ()
evalPrim EqualHere    = equalHere
evalPrim NotEqualHere = notEqualHere

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

    (_, Just (xs,memo_flag,rhs)) ->
      do -- liftIO $ putStrLn (show f ++ show as)
         ys <- sequence [ eval prog apps env a | a <- as ]
         [x] <- ifMemo memo_flag f (\ zs -> (:[]) <$> eval prog M.empty (M.fromList (zipp ("App:" ++ show f) xs zs)) rhs) ys
         return x

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

eval prog apps env (Proj e t i) =
  do obj <- eval prog apps env e
     unsafeProj obj t i

eval prog apps env (ConstraintsOf es) =
  do sequence_ [ eval prog apps env e | e <- es ]
     return (cons unit [])

eval prog apps env (EqPrim prim e1 e2) =
  do o1 <- eval prog apps env e1
     o2 <- eval prog apps env e2
     evalPrim prim o1 o2
     return (cons unit [])

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

    (_, Just (xs,memo_flag,rhs)) ->
      do -- liftIO $ putStrLn (show f ++ show as)
         case memo_flag of
           Don'tMemo ->
             do ys <- sequence [ eval prog apps env a | a <- as ]
                evalInto prog M.empty (M.fromList (zipp ("App:" ++ show f ++ "->") xs ys)) rhs res

           DoMemo ->
             do eval prog apps env (App f as) >>= (>>> res)

evalInto prog apps env (Later a) res =
  do later (evalInto prog apps env a res)

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
       [ case mc of
           Nothing -> ifNotCons y [ c | (Just c,_,_) <- alts ] (h [])
           Just c  -> ifCons y c h
       | (mc,xs,rhs) <- alts
       , let h ys = evalInto prog apps (inserts (zip xs ys) env) rhs res
       ]

evalInto prog apps env (Proj e t i) res =
  do obj <- eval prog apps env e
     pobj <- unsafeProj obj t i
     pobj >>> res


evalInto prog apps env (ConstraintsOf es) res =
  do sequence_ [ eval prog apps env e | e <- es ]

evalInto prog apps env (EqPrim prim e1 e2) res =
  do o1 <- eval prog apps env e1
     o2 <- eval prog apps env e2
     evalPrim prim o1 o2

--------------------------------------------------------------------------------------------

evalProp :: (Names n,Ord n,Show n) => Program n -> ([n],Expr n) -> M n ()
evalProp prog (vars,e) =
  do os <- sequence [ (,) v <$> newInput | v <- vars ]
     eval prog M.empty (M.fromList os) e

     let loop =
           do sequence_
                [ do s <- objectView o
                     liftIO $ putStrLn (show v ++ " = " ++ s)
                | (v,o) <- os
                ]
              mb <- trySolve
              case mb of
                Nothing -> loop
                Just b  -> return b

     b <- loop
     if b then
       do sequence_
            [ do s <- objectVal o
                 liftIO $ putStrLn (show v ++ " = " ++ show s)
            | (v,o) <- os
            ]
      else
       do return ()


--------------------------------------------------------------------------------------------

zipp :: String -> [a] -> [b] -> [(a,b)]
zipp s []     []     = []
zipp s (x:xs) (y:ys) = (x,y) : zipp s xs ys
zipp s _      _      = error ("zipp (" ++ s ++ "): unequal lengths")

inserts :: Ord a => [(a,b)] -> Map a b -> Map a b
inserts xys mp = foldr (\(x,y) -> M.insert x y) mp xys

--------------------------------------------------------------------------------------------


