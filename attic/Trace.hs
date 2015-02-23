module Trace where

import Data.IORef
import System.IO.Unsafe

data Trace a = Trace (IORef [a]) | NoTrace

newTrace :: IO (Trace a)
newTrace = Trace `fmap` newIORef []

noTrace :: Trace a
noTrace = NoTrace

trace :: Trace a -> a -> b -> b
trace NoTrace     _ y = y
trace (Trace ref) x y =
  unsafePerformIO (
    do xs <- readIORef ref
       writeIORef ref (x:xs)
       return y
  )

readTrace :: Trace a -> IO [a]
readTrace NoTrace     = return []
readTrace (Trace ref) = readIORef ref

