module Main where

import Object
import Program
import Data.Map as M

main = run test

natT = Type "Nat" [] [zer,suc]
zer  = Cons "Zer" [] natT
suc  = Cons "Suc" [natT] natT

listT t = Type "List" [t] [nil t, cns t]
nil t   = Cons "Nil"  []          (listT t)
cns t   = Cons "Cns"  [t,listT t] (listT t)

exprT   = Type "Expr" [] [cS, cK, cI, cF, cApp]
cS      = Cons "S"    [] exprT
cK      = Cons "K"    [] exprT
cI      = Cons "I"    [] exprT
cF      = Cons "F"    [] exprT
cApp    = Cons "A"    [exprT,exprT] exprT

stratT  = Type "Strat" [] [sH, sL, sR, sD]
sH      = Cons "H"     [stratT] stratT
sL      = Cons "L"     [stratT,stratT] stratT
sR      = Cons "R"     [stratT,stratT] stratT
sD      = Cons "D"     [] stratT

prog = M.fromList
  [ ("&&", (["x","y"],
      Case (Var "x")
      [ (false, [], Con false [])
      , (true, [], Var "y")
      ]
    ))

  , ("||", (["x","y"],
      Case (Var "x")
      [ (false, [], Var "y")
      , (true, [], Con true [])
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

  , ("prop1", (["xs","ys"], App "==>" [App "eqList" [App "sort" [Var "xs"], App "sort" [Var "ys"]], App "||" [App "eqList" [Var "xs", Var "ys"], App "||" [App "eqList" [App "sort" [Var "ys"], Var "ys"], App "eqList" [App "sort" [Var "xs"], Var "xs"]]]]))

  , ("step", (["e"],
      Case (Var "e")
      [ (cApp, ["i","x"],
          Case (Var "i")
          [ (cApp, ["k","g"],
              Case (Var "k")
              [ (cApp, ["s","f"],
                  Case (Var "s")
                  [ (cApp, ["a","b"], Var "e")
                  , (cS,   [],        Con cApp [Con cApp [Var "f",Var "x"], Con cApp [Var "g",Var "x"]]) 
                  , (cK,   [],        Var "e")
                  , (cI,   [],        Var "e")
                  , (cF,   [],        Var "e")
                  ]
                )
              , (cS,   [],        Var "e")
              , (cK,   [],        Var "g")
              , (cI,   [],        Var "e")
              , (cF,   [],        Var "e")
              ]
            )
          , (cS,   [],        Var "e")
          , (cK,   [],        Var "e")
          , (cI,   [],        Var "x")
          , (cF,   [],        Var "e")
          ]
        )
      , (cS,   [],        Var "e")
      , (cK,   [],        Var "e")
      , (cI,   [],        Var "e")
      , (cF,   [],        Var "e")
      ]
    ))
  
  , ("eval0", (["s", "e"],
      Case (Var "s")
      [ (sH, ["q"],     App "eval0" [Var "q", App "step" [Var "e"]])
      , (sL, ["p","q"],
          Case (Var "e")
          [ (cApp, ["a","b"], App "eval0" [Var "q", Con cApp [App "eval0" [Var "p", Var "a"],Var "b"]])
          , (cS,   [],        Var "e") 
          , (cK,   [],        Var "e")
          , (cI,   [],        Var "e")
          , (cF,   [],        Var "e")
          ]
        )
      , (sR, ["p","q"],
          Case (Var "e")
          [ (cApp, ["a","b"], App "eval0" [Var "q", Con cApp [Var "a", App "eval0" [Var "p", Var "b"]]])
          , (cS,   [],        Var "e") 
          , (cK,   [],        Var "e")
          , (cI,   [],        Var "e")
          , (cF,   [],        Var "e")
          ]
        )
      , (sD, [], Var "e")
      ]
    ))
  
  , ("eval", (["s", "e"],
      LetApp "eval1" ["s","e"] (App "eval" [Var "s", Var "e"]) $
      LetApp "eval2" ["s","e"] (App "eval" [Var "s", Var "e"]) $
      Case (Var "s")
      [ (sH, ["q"],     App "eval1" [Var "q", App "step" [Var "e"]])
      , (sL, ["p","q"],
          Case (Var "e")
          [ (cApp, ["a","b"], App "eval2" [Var "q", Con cApp [App "eval1" [Var "p", Var "a"],Var "b"]])
          , (cS,   [],        Var "e") 
          , (cK,   [],        Var "e")
          , (cI,   [],        Var "e")
          , (cF,   [],        Var "e")
          ]
        )
      , (sR, ["p","q"],
          Case (Var "e")
          [ (cApp, ["a","b"], App "eval2" [Var "q", Con cApp [Var "a", App "eval1" [Var "p", Var "b"]]])
          , (cS,   [],        Var "e") 
          , (cK,   [],        Var "e")
          , (cI,   [],        Var "e")
          , (cF,   [],        Var "e")
          ]
        )
      , (sD, [], Var "e")
      ]
    ))
  
  , ("eqExpr", (["x", "y"],
        Case (Var "x")
        [ (cApp, ["x1","x2"],
            Case (Var "y")
            [ (cApp, ["y1","y2"], App "&&" [App "eqExpr" [Var "x1", Var "y1"], App "eqExpr" [Var "x2", Var "y2"]])
            , (cS,   [],          Con false []) 
            , (cK,   [],          Con false [])
            , (cI,   [],          Con false [])
            , (cF,   [],          Con false [])
            ]
          )
        , (cS,   [],
            Case (Var "y")
            [ (cApp, ["y1","y2"], Con false [])
            , (cS,   [],          Con true []) 
            , (cK,   [],          Con false [])
            , (cI,   [],          Con false [])
            , (cF,   [],          Con false [])
            ]
          ) 
        , (cK,   [],
            Case (Var "y")
            [ (cApp, ["y1","y2"], Con false [])
            , (cS,   [],          Con false []) 
            , (cK,   [],          Con true [])
            , (cI,   [],          Con false [])
            , (cF,   [],          Con false [])
            ]
          ) 
        , (cI,   [],
            Case (Var "y")
            [ (cApp, ["y1","y2"], Con false [])
            , (cS,   [],          Con false []) 
            , (cK,   [],          Con false [])
            , (cI,   [],          Con true [])
            , (cF,   [],          Con false [])
            ]
          ) 
        , (cF,   [],
            Case (Var "y")
            [ (cApp, ["y1","y2"], Con false [])
            , (cS,   [],          Con false []) 
            , (cK,   [],          Con false [])
            , (cI,   [],          Con false [])
            , (cF,   [],          Con true [])
            ]
          ) 
        ]
    ))
  
  , ("target3", (["s", "e"], App "eqExpr" [App "eval" [Var "s", Var "e"], Con cApp [Con cF [], Var "e"]]))
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

     {-
     evalInto prog M.empty
       (M.fromList [("x",x),("y",y)])
       (len 20 (Var "x"))
       (cons true [])
     evalInto prog M.empty
       (M.fromList [("x",x),("y",y)])
       (App "prop1" [Var "x",Var "y"])
       (cons false [])
     -}
     
     evalInto prog M.empty
       (M.fromList [("x",x),("y",y)])
       (App "target3" [Var "x",Var "y"])
       (cons true [])

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
     
