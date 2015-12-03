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

listT t = Type "List" [t] [nil t, cns t]
nil t   = Cons "Nil"  []          (listT t)
cns t   = Cons "Cns"  [t,listT t] (listT t)

prog = M.fromList
  [ ("&&", (["x","y"],
      Case (Var "x")
      [ (false, [], Con false [])
      , (true, [], Var "y")
      ]
    ))

  , ("add", (["x","y"],
      Case (Var "x")
      [ (zer, [], Var "y")
      , (suc, ["x'"], Con suc [App "add" [Var "x'", Var "y"]])
      ]
    ))

  , ("target1", (["x"], atLeast' 15 (App "add" [Var "x",Var "x"])))

  , ("lt", (["x","y"],
      Case (Var "y")
      [ (zer, [], Con false [])
      , (suc, ["y'"],
          Case (Var "x")
            [ (zer, [], Con true [])
            , (suc, ["x'"], App "lt" [Var "x'", Var "y'"])
            ])
      ]
    ))

  , ("sorted", (["xs"],
      Case (Var "xs")
      [ (nil natT, [], Con true [])
      , (cns natT, ["y","ys"],
          Case (Var "ys")
          [ (nil natT, [], Con true [])
          , (cns natT, ["z","zs"], App "&&" [App "lt" [Var "y", Var "z"], App "sorted" [Var "ys"]])
          ])
      ]
    ))

  , ("target2", (["xs"], App "&&" [len 10 (Var "xs"),App "sorted" [Var "xs"]]))
  ]

atLeast' 0 e = Con true []
atLeast' n e = Case e [(zer, [], Con false []), (suc, ["x'"], atLeast' (n-1) (Var "x'"))]

len 0 e = Con true []
len n e = Case e [ (nil natT, [], Con false [])
                 , (cns natT, ["x","xs"], len (n-1) (Var "xs")) ]

test =
  do x <- newInput
     {-
     evalInto prog M.empty
       (M.fromList [("x",x)])
       (App "target1" [Var "x"])
       (cons true [])
     -}
     
     evalInto prog M.empty
       (M.fromList [("x",x)])
       (App "target2" [Var "x"])
       (cons true [])
     
     let loop =
           do s <- objectView x
              liftIO $ putStrLn ("x = " ++ s)
              mb <- trySolve
              case mb of
                Nothing -> loop
                Just b  -> return b
     
     b <- loop
     if b then
       do a <- objectVal x
          liftIO $ putStrLn ("x = " ++ show a)
      else
       do return ()
     
