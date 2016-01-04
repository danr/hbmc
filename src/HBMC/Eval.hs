{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module HBMC.Eval where

import qualified Tip.Core as Tip
import Tip.Core (Builtin())
import Tip.Core hiding (Builtin(Lit), bool)
import Tip.Pretty
import Tip.Pretty.SMT ()
import Tip.Scope
import Tip.Utils

import Control.Monad (zipWithM)

import qualified Data.Map as M
import Data.Map( Map )

data Val n
  = Con n [Val n]
  | Closure [n] (Map n (Val n)) (Expr n)
  | Thunk (Map n (Val n)) (Expr n)
  | Lit Lit
  | Unk -- wild card, can be anything
  deriving (Eq, Ord)

instance (Ord n,PrettyVar n) => Show (Val n) where
  show (Con c [])       = varStr c
  show (Con c as)       = "(" ++ unwords (varStr c:map show as) ++ ")"
  show (Thunk _ e)      = "(THUNK " ++ show (pp e) ++ ")"
  show (Closure ls _ e) = "(\\" ++ unwords (map varStr ls ++ ["->",show (pp e)]) ++ ")"
  show (Lit (Bool b))   = show b
  show (Lit (Int i))    = show i
  show Unk              = "*"

unk = Right Unk

bool = Right . Lit . Bool

-- call by need (not by name) evaluator

-- for instance bsort contains a let that needs to be evaluated lazily to
-- not cause non-termination

evalExpr :: forall n . (Show n,PrettyVar n,Ord n) => Theory n -> Map n (Val n) -> Expr n -> Either String (Val n)
evalExpr thy u v = deep =<< go u v
  where
  deep (Con n vs) = Con n <$> mapM deep vs
  deep t@Thunk{}  = deep =<< force t
  deep e          = return e

  force (Thunk m e) = force =<< go m e
  force e           = return e

  go m e0 =
    case e0 of
      Lcl (Local l _) -> maybe (Left "Variable not in scope") Right (M.lookup l m)
      hd :@: es ->
        do let vs = [ Thunk m e | e <- es ]
           case hd of
             Gbl (Global f _ _)
               | Just (ConstructorInfo _ (Constructor c _ _)) <- lookupGlobal f scp
               -> return (Con c vs)
               | Just Function{..} <- M.lookup f fns
               -> go (M.fromList (map lcl_name func_args `zip` vs)) func_body
               | otherwise
               -> Left $ "Unknown global: " ++ varStr f
             Builtin At ->
               do let f:args = vs
                  Closure as cls lam_body <- force f
                  go (M.fromList (as `zip` args) `M.union` cls `M.union` m) lam_body
             Builtin b ->
               do evalBuiltin b =<< mapM deep vs
      Lam ls b ->
        do let fvs = map lcl_name (free e0 :: [Local n])
           return (Closure (map lcl_name ls) (M.filterWithKey (\ x _ -> x `elem` fvs) m) b)
      Let (Local x _) e1 e2 ->
        do go (M.insert x (Thunk m e1) m) e2
      Match e brs ->
        do v <- force =<< go m e
           case v of
             Unk -> unk
             _   ->
               do let match (Lit l)    (Case (LitPat l') rhs:_)                  | l == l' = Right (M.empty,rhs)
                      match (Con c as) (Case (ConPat (Global g _ _) args) rhs:_) | c == g  = Right (M.fromList (map lcl_name args `zip` as),rhs)
                      match _ [Case Default rhs] = Right (M.empty,rhs)
                      match x (_:ps) = match x ps
                      match _ _      = Left $ "No matching pattern " ++ show v ++ " " ++ show [ p | Case p _ <- brs ]
                  (m',rhs) <- match v (reverse brs) -- reverse so default is last
                  go (m' `M.union` m) rhs
      Quant{} -> Left "Evaluation of Quantifier"

  scp = scope thy

  fns = M.fromList [ (func_name fn,fn) | fn <- thy_funcs thy ]

equal :: forall n . (PrettyVar n,Show n,Ord n) => Val n -> Val n -> Either String (Val n)
equal (Con n vs)  (Con n2 vs2) = do xs <- zipWithM equal vs vs2
                                    evalBuiltin And ((Lit (Bool (n == n2)):xs) :: [Val n])
equal (Lit l)     (Lit l2)     = bool (l == l2)
equal Unk         _            = unk
equal _           Unk          = unk
equal c@Closure{} _            = Left $ "equality on" ++ show c
equal _           c@Closure{}  = Left $ "equality on" ++ show c
equal c@Thunk{}   _            = Left $ "equality on" ++ show c
equal _           c@Thunk{}    = Left $ "equality on" ++ show c
equal _           _            = bool False

evalBuiltin :: (PrettyVar n,Show n,Ord n) => Builtin -> [Val n] -> Either String (Val n)
evalBuiltin b vs =
  case b of
    At -> error "At"
    Tip.Lit lit -> Right $ Lit lit
    And -> head $ [ Right l | l@(Lit (Bool False)) <- vs ] ++ [ unk | Unk <- vs ] ++ [ bool True  ]
    Or  -> head $ [ Right l | l@(Lit (Bool True )) <- vs ] ++ [ unk | Unk <- vs ] ++ [ bool False ]
    Not -> case vs of
             [Unk] -> unk
             [Lit (Bool b)] -> bool (not b)
             _ -> Left $ "Malformed Not: " ++ show vs
    Implies -> case vs of
                 [u1,u2] -> evalBuiltin Or =<< sequence [evalBuiltin Not [u1],return u2]
                 _ -> Left $ "Malformed Implies: " ++ show vs
    Equal    -> case vs of
                  a:as -> evalBuiltin And =<< mapM (a `equal`) as
                  []   -> bool False
    Distinct -> evalBuiltin And =<<
                  sequence [ evalBuiltin Not =<< sequence [a `equal` b]
                           | (a,bs) <- withPrevious vs, b <- bs
                           ]
    IntAdd -> intop (+)
    IntSub -> intop (-)
    IntMul -> intop (*)
    IntDiv -> intop div
    IntMod -> intop mod
    IntGt  -> cmpop (>)
    IntGe  -> cmpop (>=)
    IntLt  -> cmpop (<)
    IntLe  -> cmpop (<=)
  where
  guarded ok = case [ Unk | Unk <- vs ] of
                 _:_ -> unk
                 _   -> ok
  intop (#) = guarded $ Right (Lit (Int (foldr1 (#) [ v | Lit (Int v) <- vs ])))
  cmpop (#) = guarded $ case vs of
                          [ Lit (Int a), Lit (Int b) ] -> bool (a # b)
                          _ -> Left "Cmp not on two ints"
