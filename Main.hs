module Main where

import Object
import Program
import Data.Map as M

main = run test

natT = Type "Nat" [] [zer,suc]
zer  = Cons "Zer" [] natT
suc  = Cons "Suc" [natT] natT

boolT = Type "Bool"  [] [false,true]
false = Cons "False" [] boolT
true  = Cons "True"  [] boolT

prog = M.fromList
  [ ("add", (["x","y"],
      Case (Var "x")
      [ (zer, [], Var "y")
      , (suc, ["x'"], Con suc [App "add" [Var "x'", Var "y"]])
      ]
    ))
  , ("prop", (["x"], atLeast 5 (App "add" [Var "x",Var "x"])))
  ]
 where
  atLeast 0 e = Con true []
  atLeast n e = Case e [(zer, [], Con false []), (suc, ["x'"], atLeast (n-1) (Var "x'"))]

test =
  do x <- newInput
     b <- eval prog M.empty (M.fromList [("x",x)]) (App "prop" [Var "x"])
     isCons b true $ \_ -> return ()
     
     let loop =
           do mb <- trySolve
              case mb of
                Nothing -> loop
                Just b  -> return b
     
     b <- loop
     if b then
       do a <- objectVal x
          liftIO $ print a
      else
       do return ()
     
