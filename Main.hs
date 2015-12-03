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

  , ("==>", (["x","y"],
      Case (Var "x")
      [ (false, [], Con true [])
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

  , ("leq", (["x","y"],
      Case (Var "x")
      [ (zer, [], Con true [])
      , (suc, ["x'"],
          Case (Var "y")
            [ (zer, [], Con false [])
            , (suc, ["y'"], App "leq" [Var "x'", Var "y'"])
            ])
      ]
    ))

  , ("eqNat", (["x","y"],
      Case (Var "x")
      [ (zer, [],
          Case (Var "y")
            [ (zer, [], Con true [])
            , (suc, ["y'"], Con false [])
            ])
      , (suc, ["x'"],
          Case (Var "y")
            [ (zer, [], Con false [])
            , (suc, ["y'"], App "eqNat" [Var "x'", Var "y'"])
            ])
      ]
    ))

  , ("eqList", (["xs","ys"],
      Case (Var "xs")
      [ (nil natT, [],
          Case (Var "ys")
            [ (nil natT, [], Con true [])
            , (cns natT, ["z","zs"], Con false [])
            ])
      , (cns natT, ["z","zs"],
          Case (Var "ys")
            [ (nil natT, [], Con false [])
            , (cns natT, ["w","ws"], App "&&" [App "eqNat" [Var "z", Var "w"], App "eqList" [Var "zs", Var "ws"]])
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

  , ("sort", (["xs"],
      Case (Var "xs")
      [ (nil natT, [], Con (nil natT) [])
      , (cns natT, ["y","ys"], App "insert" [Var "y", App "sort" [Var "ys"]])
      ]
    ))

  , ("insert", (["x","xs"],
      Case (Var "xs")
      [ (nil natT, [], Con (cns natT) [Var "x", Con (nil natT) []])
      , (cns natT, ["y","ys"], Case (App "leq" [Var "x", Var "y"])
                               [ (true,  [], Con (cns natT) [Var "x", Var "xs"])
                               , (false, [], Con (cns natT) [Var "y", App "insert" [Var "x", Var "ys"]])
                               ])
      ]
    ))

  , ("prop1", (["xs","ys"], App "==>" [App "eqList" [App "sort" [Var "xs"], App "sort" [Var "ys"]], App "eqList" [Var "xs", Var "ys"]]))
  ]

atLeast' 0 e = Con true []
atLeast' n e = Case e [(zer, [], Con false []), (suc, ["x'"], atLeast' (n-1) (Var "x'"))]

len 0 e = Con true []
len n e = Case e [ (nil natT, [], Con false [])
                 , (cns natT, ["x","xs"], len (n-1) (Var "xs")) ]

test =
  do x <- newInput
     y <- newInput
     {-
     evalInto prog M.empty
       (M.fromList [("x",x)])
       (App "target1" [Var "x"])
       (cons true [])
     -}
     
     {-
     evalInto prog M.empty
       (M.fromList [("x",x)])
       (App "target2" [Var "x"])
       (cons true [])
     -}

     evalInto prog M.empty
       (M.fromList [("x",x),("y",y)])
       (App "prop1" [Var "x",Var "y"])
       (cons false [])
     
     let loop =
           do s <- objectView x
              liftIO $ putStrLn ("x = " ++ s)
              s <- objectView y
              liftIO $ putStrLn ("y = " ++ s)
              mb <- trySolve
              case mb of
                Nothing -> loop
                Just b  -> return b
     
     b <- loop
     if b then
       do a <- objectVal x
          liftIO $ putStrLn ("x = " ++ show a)
          b <- objectVal y
          liftIO $ putStrLn ("y = " ++ show b)
      else
       do return ()
     
