{-# LANGUAGE DeriveDataTypeable #-}
module HBMC.Params where

import System.Console.CmdArgs

data Params =
  Params
    { file                 :: String
--     , depth                :: Maybe Int
--     , upfront              :: Bool
     , merge                :: Bool
     , memo                 :: Bool
     , quiet                :: Bool
     , debug                :: Bool
--     , conflict_minimzation :: Bool
--     , delay_all_datatypes  :: Bool
--     , insist_isnt          :: Bool
--     , postpone             :: Bool
--     , strict_data_lazy_fun :: Bool
    , prop_names           :: Maybe [String]
    }
  deriving (Show,Data,Typeable)

defParams :: Params
defParams =
  Params
    { file                 = ""      &= argPos 0 &= typFile
--    , depth                = Nothing &= name "d"   &= help "Maximum depth of counterexamples (unlimited)"
--    , upfront              = False   &= name "u"   &= help "Generate input data upfront (only applies with depth)"
    , merge                = True    &= name "f"   &= help "Merge function calls             (on)"
    , memo                 = True    &= name "m"   &= help "Memoise recursive functions      (on)"
    , quiet                = False   &= name "q"   &= help "Be quiet"
    , debug                = False   &= name "dbg" &= help "Print debug info"
--    , conflict_minimzation = False   &= name "c"   &= help "Minimize conflicts"
--    , delay_all_datatypes  = False   &= name "l"   &= help "Delay all datatypes"
--    , insist_isnt          = False   &= name "i"   &= help "Insist isn't when possible"
--    , postpone             = True                  &= help "Use postpone                     (on)"
--    , strict_data_lazy_fun = False   &= name "s"   &= help "Always use postpone, make case strict"
    , prop_names           = Nothing &= name "prop" &= help "Property to consider (default: first)"
    }
  &= program "hbmc" &= summary logo

logo :: String
logo = map (\ x -> if x == 'z' then '\\' else x) $ unlines
    [ "  _     _                 "
    , " | |   | | SYMBØ VERSION  "
    , " | |__ | |__  _____  ___  "
    , " | '_ z| '_ z| ' ' z/ __| "
    , " | | | | |_) | | | | (__  "
    , " |_| |_|_.__/|_|_|_|z___| "
    , " Dan Rosén, Koen Claessen "
    , " {danr,koen}@chalmers.se  "
    ]

getParams :: IO Params
getParams = cmdArgs defParams

