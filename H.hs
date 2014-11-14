module H where

import Symbolic
import MiniSat
import Control.Applicative

--------------------------------------------------------------------------------

newtype H a = H{ run :: Solver -> [Bit] -> IO (Maybe a) }

instance Applicative H where
  pure x      = H (\_ _ -> return (Just x))
  H f <*> H x = H (\s ctx -> do mf <- f s ctx
                                case mf of
                                  Nothing -> return Nothing
                                  Just f  -> do mx <- x s ctx
                                                case mx of
                                                  Nothing -> return Nothing
                                                  Just x  -> return (Just (f x)))

instance Functor H where
  f `fmap` H m = H (\s ctx -> do mx <- m s ctx
                                 return (f `fmap` mx))

instance Monad H where
  return    = pure
  H m >>= k = H (\s ctx -> do mx <- m s ctx
                              case mx of
                                Nothing -> return Nothing
                                Just x  -> run (k x) s ctx)

--------------------------------------------------------------------------------

withExtra :: H a -> Bit -> H a
H m `withExtra` b = H (\s ctx -> m s (b:ctx))

impossible :: H a
impossible = H (\s ctx -> do addClauseBit s (map nt ctx)
                             return Nothing)

lift :: H a -> H (Lift a)
lift (H m) = H (\s ctx -> do mx <- m s ctx
                             return (Just (case mx of
                                             Nothing -> UNR
                                             Just x  -> The x)))
peek :: Lift a -> H a
peek UNR     = H (\_ _ -> return Nothing)
peek (The x) = return x 

withSolver :: (Solver -> IO a) -> H a
withSolver f = H (\s _ -> Just `fmap` f s)

--------------------------------------------------------------------------------

ifThenElse :: Symbolic a => Bit -> a -> a -> H a
ifThenElse c x y = withSolver (\s -> iff s c x y)

match :: Symbolic a => SymTerm -> [(Name, [SymTerm] -> H a)] -> H a
match t alts = H (\s ctx ->
  do lx <- switch s t [ (c, \b xs -> do my <- run (alt xs) s (b:ctx)
                                        return (case my of
                                                  Nothing -> UNR
                                                  Just y  -> The y))
                      | (c, alt) <- alts
                      ]
     return (case lx of
               UNR   -> Nothing
               The x -> Just x)
  )

--------------------------------------------------------------------------------

