{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module HBMC.Live where

import HBMC.Params
import HBMC.Lib     hiding (Con,Call)
import HBMC.Monadic

import Tip.Pretty

import Data.Maybe (isJust)
import Data.Map (Map)
import qualified Data.Map as M

data Static a =
  Static
    { lkup_desc :: a -> LiveDesc a
    , lkup_func :: a -> [LiveData a] -> H (LiveData a)
    , params    :: Params
    }

data Dynamic a =
  Dynamic
    { var_map  :: Map a (LiveData a)
    , proj_map :: Map a [LiveData a]
    , pred_map :: Map a (Val a)
    }

data LiveEnv a =
  LiveEnv
    { static  :: Static a
    , dynamic :: Dynamic a
    }

newEnv :: Ord a => Static a -> [(a,LiveData a)] -> LiveEnv a
newEnv st vs = LiveEnv st (Dynamic (M.fromList vs) M.empty M.empty)

liveProp :: forall a . (Show a,PrettyVar a,Ord a) => Params -> Static a -> Prop a -> IO ()
liveProp p st (Prop vs m) =
  run p $ do dyn <- liveMon (newEnv st []) m
             solveAndSee (Tagged [ (varStr v,var_map dyn ! v) | v <- vs ])

liveFuncs :: (Show a,PrettyVar a,Ord a) => Params -> (a -> LiveDesc a) -> [Func a] -> Static a
liveFuncs p lkup_desc funcs = st
  where
  tbl         = [ (name,liveFunc st f) | f@(Func name _ _ _ _ _ _) <- funcs ]
  st          = Static lkup_desc lkup_func p
  lkup_func x = case lookup x tbl of Just func -> func
                                     Nothing   -> error $ "Function not found:" ++ varStr x

liveFunc :: (Show a,PrettyVar a,Ord a) => Static a -> Func a -> [LiveData a] -> H (LiveData a)
liveFunc st (Func fname as_vars r_var r_ty mem chk m) =
  (if mem then memoWith else nomemoWith)
    (newData Nothing False False (lkup_desc st r_ty))
    (varStr fname) $
      \ as r ->
         (if chk then check else id)
         (liveMon (newEnv st ((r_var,r):as_vars `zip` as)) m >> return ())

liveMon :: (Show a,PrettyVar a,Ord a) => LiveEnv a -> Mon a -> H (Dynamic a)
liveMon env []         = return (dynamic env)
liveMon env (act:acts) =
  do let LiveEnv{..} = env
         Dynamic{..} = dynamic
         Static{..}  = static
         rec_with dyn as = liveMon env{ dynamic = dyn } as
     case act of
       _ :<-: _ -> return () -- NOTE: handled below

       InsistIsn't r c ->
         do caseData (var_map ! r) $ \ v _ -> addClauseHere [nt (v =? c)]

       Guard g ps m ->
         do bs <- mapM (livePred env) ps
            case g of
              Unless -> unless bs (liveMon env m >> return ())
              When   -> whens  bs (liveMon env m >> return ())

       CaseData _ s v_var as_var m ->
         do caseData (liveSimp env s) $
              \ v as ->
                do rec_with dynamic{ proj_map = M.insert as_var as proj_map
                                   , pred_map = M.insert v_var v pred_map
                                   }
                            m
                   return ()

       BinPrim bp s1 s2 ->
         do let d1 = liveSimp env s1
                d2 = liveSimp env s2
            case bp of
              EqualHere    -> equalHere    d1 d2
              NotEqualHere -> notEqualHere d1 d2

       s :>>>: x -> liveSimp env s >>> (var_map ! x)

     case act of
       v :<-: rhs ->
         do x <- case rhs of
                New i tc  -> newData (if i then depth params else Nothing)
                                     (i && upfront params && isJust (depth params))
                                     i
                                     (lkup_desc tc)
                Call f ss -> lkup_func f (map (liveSimp env) ss)
            rec_with (dynamic { var_map = M.insert v x var_map }) acts

       _ -> liveMon env acts

livePred :: (Show a,Ord a) => LiveEnv a -> Pred a -> H Bit
livePred env (v :=? x) = (pred_map (dynamic env) ! v) ==? x

liveSimp :: (Show a,Ord a) => LiveEnv a -> Simp a -> LiveData a
liveSimp env (Con tc k ss) = conData (lkup_desc (static env) tc) k (map (liveSimp env) ss)
liveSimp env (Proj i x)    = let v:_ = drop i (proj_map (dynamic env) ! x) in v
liveSimp env (Var x)       = var_map (dynamic env) ! x

(!) :: (Show k,Show v,Ord k) => Map k v -> k -> v
m ! k = case M.lookup k m of Just v  -> v
                             Nothing -> error $ "Cannot find: " ++ show k

