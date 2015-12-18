module Lambdas where

-- import Control.Monad(guard,join)
-- import Data.Maybe(isJust)

-- import Test.LazySmallCheck
-- import Control.Enumerable.LazySearch

import qualified Prelude
import Tip.Prelude

type N = Nat

type Var = N

data Type = TBool | TUnit | TFun Type Type
  deriving (Prelude.Eq, Prelude.Show)

TBool `eq` TBool = True
TUnit `eq` TUnit = True
TFun a b `eq` TFun u v = (a `eq` u) && (b `eq` v)
_ `eq` _ = False

data Exp = Lam Var Exp
         | App Exp (Exp, Type)
         | Var Var
         | Lit Lit
         | Let [(Type, Var, Exp)] Exp
  deriving (Prelude.Eq, Prelude.Show)

data Lit = VBool Bool
         | VUnit
  deriving (Prelude.Eq, Prelude.Show)





tc :: Exp -> Type -> Bool
tc = go [] where
  go :: [(Var, Type)] -> Exp -> Type -> Bool
  go env e0 t0 = case e0 of
    Lam v e
      | TFun t1 t2 <- t0 -> go ((v,t1):env) e t2
      | otherwise        -> False
    App e1 (e2,t2) ->
      go env e2 t2 &&
      go env e1 (TFun t2 t0)
    Var v          -> case lookup v env of
                       Just t  -> t `eq` t0
                       Nothing -> False
    Lit (VBool _)  -> t0 `eq` TBool
    Lit VUnit      -> t0 `eq` TUnit
    Let ds e       ->
      let tclet _ env' []              = go env' e t0
          tclet used env' ((t,v,e'):ds) = not (v `elem` used)
                                       && go env' e' t
                                       && tclet (v:used) ((v,t):env') ds
      in tclet [] env ds
    -- _              -> False



type Env = [(Var, Val)]

data Val =
         -- VFun (Val -> Maybe Val)
         VFun Env Var Exp
         | VLit Lit


eval' :: Exp -> Maybe Lit
eval' e = case eval e of
            Just (VLit x) -> Just x
            _ -> Nothing

eval :: Exp -> Maybe Val
eval = go [] where
  go :: Env -> Exp -> Maybe Val
  go env e0 = case e0 of
    Lam v e         -> Just $ VFun env v e
    App e1 (e2, t)
      | Just (VFun env' v ef) <- go env e1
      , Just a <- go env e2
      -> go ((v,a):env') ef

    Var v           -> lookup v env
    Lit a           -> Just (VLit a)
    Let xs e | Just env' <- evlet env xs -> go env' e

    _ -> Nothing

  evlet :: Env -> [(Type,Var, Exp)] -> Maybe Env
  evlet env' [] = Just env'
  evlet env' ((_,v,e):ves)
    | Just x <- go env' e = evlet ((v,x):env') ves
    | otherwise = Nothing

elimlet :: Exp -> Maybe Exp
elimlet e = case e of
  Lam v e | Just e' <- elimlet e -> Just (Lam v e')
          | otherwise -> Nothing

  App e1 (e2,t) -> case elimlet e1 of
    Nothing  -> case elimlet e2 of
                  Just e2' -> Just (App e1 (e2',t))
                  Nothing  -> Nothing
    Just e1' -> Just (App e1' (e2,t))
  Var v         -> Nothing
  Lit x         -> Nothing
  Let [] e      -> elimlet e
  Let ((_,v,ev):xs) e -> Just (Let [(t,v2,subst v ev ex) | (t,v2,ex) <- xs] (subst v ev e))



subst v ev e0@(Lam v1 e)
  | v == v1   = e0
  | otherwise = Lam v1 (subst v ev e)
subst v ev (App e1 (e2,t)) = App (subst v ev e1) (subst v ev e2,t)
subst v ev e@(Var v1)  | v == v1    = ev
                       | otherwise  = (Var v1)
subst v ev e@(Lit x)  = e
subst v ev (Let xs e) = Let [(t,v2,subst v ev ex) | (t,v2,ex) <- xs] (subst v ev e)

fromMaybe x Nothing  = x
fromMaybe _ (Just y) = y

prop_elimlet e = tc e TBool ==> eval' e === eval' (fromMaybe e (elimlet e))


{-

r1 n = search n (not . prop_elimlet)

s1 = test prop_elimlet

instance Enumerable N where
  enumerate = datatype [c0 Z, c1 S]

instance Enumerable Type where
  enumerate = datatype [c0 TBool, c0 TUnit, c2 TFun]

instance Enumerable Exp where
  enumerate = datatype [c2 Lam, c2 App, c1 Var, c1 Lit, c2 Let]

instance Enumerable Lit where
  enumerate = datatype [c1 VBool, c0 VUnit]


instance Serial N where
  series = cons0 Z \/ cons1 S

instance Serial Type where
  series = cons0 TBool \/ cons0 TUnit \/ cons2 TFun

instance Serial Lit where
  series = cons1 VBool \/ cons0 VUnit

instance Serial Exp where
  series = cons2 Lam \/ cons2 App \/ cons1 Var \/ cons1 Lit \/ cons2 Let
   -- \/ cons0 Undefined
-}
