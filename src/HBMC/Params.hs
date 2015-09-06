{-# LANGUAGE DeriveDataTypeable #-}
module HBMC.Params where

import System.Console.CmdArgs

data Params =
  Params
    { file                 :: String
    , compile              :: Bool
    , merge                :: Bool
    , memo                 :: Bool
    , quiet                :: Bool
    , debug                :: Bool
    , conflict_minimzation :: Bool
    , delay_all_datatypes  :: Bool
    , prop_names           :: Maybe [String]
    }
  deriving (Show,Data,Typeable)

defParams :: Params
defParams =
  Params
    { file                 = ""      &= argPos 0 &= typFile
    , compile              = False   &= name "g" &= help "Compile and run"
    , merge                = True    &= name "f" &= help "Merge function calls          (on)"
    , memo                 = True    &= name "m" &= help "Memoise recursive functions   (on)"
    , quiet                = False   &= name "q" &= help "Be quiet"
    , debug                = False   &= name "d" &= help "Print debug info"
    , conflict_minimzation = False   &= name "c" &= help "Minimize conflicts"
    , delay_all_datatypes  = False   &= name "l" &= help "Delay all datatypes"
    , prop_names           = Nothing &= name "prop" &= help "Property to consider (default: first)"
    }
  &= program "hbmc" &= summary logo

logo :: String
logo = map (\ x -> if x == 'z' then '\\' else x) $ unlines
    [ "  _     _                 "
    , " | |   | |                "
    , " | |__ | |__  _____  ___  "
    , " | '_ z| '_ z| ' ' z/ __| "
    , " | | | | |_) | | | | (__  "
    , " |_| |_|_.__/|_|_|_|z___| "
    , " Dan Rosén, Koen Claessen "
    , " {danr,koen}@chalmers.se  "
    ]

getParams :: IO Params
getParams = cmdArgs defParams

