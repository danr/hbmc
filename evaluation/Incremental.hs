module Main where

import System.Directory
import System.FilePath
import Control.Applicative

import System.Environment
import System.Process
import System.Exit

import Data.Time.Clock
import Numeric
import Text.Printf

import Data.Char
import Data.List
import Data.List.Split
import Data.Ord
import Data.Function
import System.Timeout

import System.Directory
import System.FilePath.Find as F

import qualified Control.Exception as C
import Control.DeepSeq (rnf)

timeIt :: IO a -> IO (Double,a)
timeIt m =
  do t0 <- getCurrentTime
     r <- m
     t1 <- getCurrentTime
     let t :: Double
         t = fromRat (toRational (diffUTCTime t1 t0))
     return (t,r)

depths :: [Int]
depths = [1..20] ++ [30,40..100] ++ [200,300..1000]

main = do
  all_args@(use_depths0:bad:dir:timelimit:cmd:args) <- getArgs
  files <- F.find always (fileName ~~? "*.smt2" ||? fileName ~~? "*.bin") dir

  let use_depths = read use_depths0

  let is_ok = case bad of
        "-" -> const True
        _   -> \ u -> and [ not ([ if b == '_' then ' ' else b | b <- bad' ] `isInfixOf` u)
                          | bad' <- splitOn "-" bad
                          ]

      log_filename d = "results/" ++ (concatMap (++ "_") (cmd:args)) ++ (if use_depths then "_" ++ show d else "")

      log :: Int -> FilePath -> Maybe Double -> IO ()
      log d f maybe_time =
        do let time_str = case maybe_time of
                            Just t  -> printf "%0.5f" t
                            Nothing -> "-"
           appendFile (log_filename d) (f ++ "," ++ time_str ++ "\n")

  -- putStrLn log_filename
  print all_args

  logs <-
        sequence
      [ do b <- doesFileExist (log_filename d)
           if b then do s <- readFile (log_filename d)
                        return (d,[ f | l <- lines s, let (f,',':_) = break (== ',') l ])
                else return (d,[])
      | d <- if use_depths then depths else [0]
      ]

  C.evaluate (rnf logs)

  let exists f d =
        case lookup d logs of
          Just files -> f `elem` files
          Nothing    -> False

  let process []     _ = return ()
      process (d:ds) f | exists f d = process ds f
      process (d:ds) f =
        do putStrLn $ show d ++ " " ++ f
           let args' | use_depths = args ++ [show d]
                     | otherwise  = args
           let full_cmd = case cmd of
                 '_':_ -> (timelimit:f:args')
                 _     -> (timelimit:cmd:f:args')
           (t,(exc,out,err)) <- timeIt (readProcessWithExitCode "timeout" full_cmd "")
           putStrLn (printf "%0.5fs" t ++ ", " ++ show exc)
           putStrLn out
           putStrLn err
           case exc of
             ExitSuccess | is_ok out
               -> do log d f (Just t)
                     process ds f
             _ -> do sequence_ [ log d' f Nothing | d' <- d:ds ]

  mapM_ (process (if use_depths then depths else [0])) files

