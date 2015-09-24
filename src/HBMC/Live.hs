{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module HBMC.Live where

import HBMC.Params  hiding (memo)
import HBMC.Lib     hiding (Con,Call)
import HBMC.Monadic

import Tip.Pretty

import Data.Map (Map)
import qualified Data.Map as M

data Static a =
  Static
    { lkup_desc :: a -> DataDesc a
    , lkup_func :: a -> [Delayed a] -> H (Delayed a)
    }

data Dynamic a =
  Dynamic
    { var_map  :: Map a (Delayed a)
    , proj_map :: Map a [Delayed a]
    }

data LiveEnv a =
  LiveEnv
    { static  :: Static a
    , dynamic :: Dynamic a
    }

newEnv :: Ord a => Static a -> [(a,Delayed a)] -> LiveEnv a
newEnv st vs = LiveEnv st (Dynamic (M.fromList vs) M.empty)

liveProp :: forall a . (Show a,PrettyVar a,Ord a) => Params -> Static a -> Prop a -> IO ()
liveProp p st (Prop vs m) =
  run $ do dyn <- fst <$> liveMon (newEnv st []) m
           solveAndSee
             (conflict_minimzation p)
             (quiet p) (not (quiet p))
             (Tagged [ (varStr v,var_map dyn ! v) | v <- vs ])

liveFuncs :: (Show a,PrettyVar a,Ord a) => (a -> DataDesc a) -> [Func a] -> Static a
liveFuncs lkup_desc funcs = st
  where
  tbl         = [ (name,liveFunc st f) | f@(Func name _ _ _ _ _) <- funcs ]
  st          = Static lkup_desc lkup_func
  lkup_func x = case lookup x tbl of Just func -> func
                                     Nothing   -> error $ "Function not found:" ++ varStr x

liveFunc :: (Show a,PrettyVar a,Ord a) => Static a -> Func a -> [Delayed a] -> H (Delayed a)
liveFunc st (Func fname as_vars _res_ty mem chk m) =
  (if mem then memo else nomemo) (varStr fname)
    $ \ as ->
         (if chk then check else id)
         (snd <$> liveMon (newEnv st (as_vars `zip` as)) m)

liveRet :: (Show a,PrettyVar a,Ord a) => LiveEnv a -> Ret a -> H (Delayed a)
liveRet env ret =
  case ret of
    Simp s    -> return (liveSimp env s)
    Unit      -> delay False (error "liveRet: Looking at a unit value")
    Dead      -> delay False (error "liveRet: Looking at a dead value")
    CaseRet c -> liveCase env c

liveCase :: (Show a,PrettyVar a,Ord a) => LiveEnv a -> Case a -> H (Delayed a)
liveCase env (Case tc s as_var ks) =
  do -- io (putStrLn $ "caseDelayed on " ++ show tc ++ " " ++ show s)
     caseDelayed (liveSimp env s)
       [ (c,\ as -> do let env' = env{ dynamic = (dynamic env){
                                         proj_map = M.insert as_var as (proj_map (dynamic env))
                                     } }
                       snd <$> liveMon env' m)
       | (c,m) <- ks
       ]

liveMon :: forall a . (Show a,PrettyVar a,Ord a) => LiveEnv a -> Mon a -> H (Dynamic a,Delayed a)
liveMon env (Mon acts ret) = go env acts
  where
  go :: LiveEnv a -> [Act a] -> H (Dynamic a,Delayed a)
  go env []         = (,) (dynamic env) <$> liveRet env ret
  go env (act:acts) =
    do let LiveEnv{..} = env
           Dynamic{..} = dynamic
           Static{..}  = static
           rec          = go env acts
           rec_with dyn = go env{ dynamic = dyn } acts
       case act of
         v :<-: rhs ->
           do x <- case rhs of
                  New i tc  -> do d <- newDelayed i (lkup_desc tc)
                                  io (putStrLn $ "New: " ++ show v ++ " " ++ show i ++ " " ++ show tc ++ ":" ++ show d)
                                  return d
                  Call f ss -> lkup_func f (map (liveSimp env) ss)
                  CaseRhs c -> liveCase env c
              rec_with (dynamic { var_map = M.insert v x var_map })

         {-
         InsistIsn't r c ->
           do caseData (var_map ! r) $ \ v _ -> addClauseHere [nt (v =? c)]
         -}

         BinPrim bp s1 s2 ->
           do let d1 = liveSimp env s1
                  d2 = liveSimp env s2
              case bp of
                EqualHere    -> equalHere    d1 d2
                NotEqualHere -> notEqualHere d1 d2
              rec

         s :>>>: x ->
           do liveSimp env s >>> (var_map ! x)
              rec

liveSimp :: (Show a,Ord a) => LiveEnv a -> Simp a -> Delayed a
liveSimp env (Con tc k ss) = conDelayed (lkup_desc (static env) tc) k (map (liveSimp env) ss)
liveSimp env (Proj i x)    = let v:_ = drop i (proj_map (dynamic env) ! x) in v
liveSimp env (Var x)       = var_map (dynamic env) ! x

(!) :: (Show k,Show v,Ord k) => Map k v -> k -> v
m ! k = case M.lookup k m of Just v  -> v
                             Nothing -> error $ "Cannot find: " ++ show k

