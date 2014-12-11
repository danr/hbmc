{-# LANGUAGE TypeFamilies #-}

import Symbolic
import Str
import Data.List
import Control.Monad

--------------------------------------------------------------------------------

infix 4 ::-
infix 5 :->

--------------------------------------------------------------------------------

type Arg     = Int
type Word    = String
type Token   = Val (Either Word Arg)
type StrExpr = [Token]

newStrExpr :: Int -> H Token -> H StrExpr
newStrExpr k newTok =
  do ts <- sequence [ newTok | i <- [1..k] ]
     sequence_ [ addClause [nt (t1 =? Right 0), t2 =? Right 0] | (t1,t2) <- ts `zip` tail ts ]
     return ts

newLin :: [Word] -> Int -> Int -> H ([String] -> H String, [Str Word] -> H (Str Word))
newLin ws k ar =
  do ts <- newStrExpr k tok
     
     let getDef xs =
           do ws <- sequence [ get t | t <- ts ]
              return $
                let s = concat (intersperse " + " [ showTok w xs | w <- ws, w /= Right 0 ]) in
                  if null s then show "" else s
         
         lin xs =
           do ys <- sequence [ arg t xs | t <- ts ]
              return (concatt ys)
     
         arg st xs =
           choose st $ \t ->
             case t of
               Left w  -> do return (unit w)
               Right 0 -> do return empty
               Right i -> do return (xs !! (i-1))
     
     return (getDef, lin)
 where
  tok = newVal ([ Left w | w <- ws ] ++ [ Right i | i <- [0..ar] ])

  showTok (Left w)  _  = "\"" ++ w ++ "\""
  showTok (Right i) xs = xs !! (i-1)

--------------------------------------------------------------------------------

type Lin = ([Str Word], Val Int)

tuple [x] = x
tuple xs  = "(" ++ concat (intersperse ", " xs) ++ ")"

newGrammar :: [Word] -> [(Fun,Int)] -> H (H String, Tree -> H Lin)
newGrammar ws fs =
  do table <- sequence
              [ do gs <- sequence
                         [ do shs <- sequence [ newLin ws k (arity f) | j <- [1..rarity f] ]
                              p   <- newVal [0..pk-1]
                              return ( \xs -> sequence [ h xs | (_,h) <- shs ]
                                     , p
                                     , \xs ->
                                         do i <- get p
                                            ss <- sequence [ s xs | (s,_) <- shs ]
                                            return (tuple (ss ++ [ show i | pk > 1 ]))
                                     )
                         | i <- [1..n]
                         ]
                   return (f,gs)
              | (f@(_ ::- xs :-> (_, _, pk)),k) <- fs
              , let n = product [ pk | (_, _, pk) <- xs ]
              ]

     let apply :: Fun -> [Lin] -> H Lin
         apply f ls =
           do vp <- parameters [ p | (_,p) <- ls ]
              choose vp $ \p ->
                let (h,q,_) = fs !! p in
                  do ys <- h (concat [ xs | (xs,_) <- ls ])
                     return (ys,q)
          where
           fs:_ = [ fs | (g,fs) <- table, g == f ]
          
           parameters []     = do return (val 0)
           parameters (p:ps) = do q <- parameters ps
                                  pq <- cross p q
                                  return (vmap (\(x,y) -> x + length (domain p) * y) pq)
     
         lin :: Tree -> H Lin
         lin (App f ts) =
           do ls <- sequence [ lin t | t <- ts ]
              apply f ls

         getDefs :: H String
         getDefs =
           do ds <- sequence
                    [ do rhs <- sequence [ sh as' | (_,_,sh) <- fs ]
                         return $ unlines $
                           [ f ++ " :: " ++ showType xs y
                           , f ++ concat [ " " ++ a | a <- as ]
                           ] ++
                           [ "  " ++ (if null ps then "= " else "| " ++ concat (intersperse " & " ps) ++ " = ")
                                  ++ r
                           | (r,is) <- rhs `zip` iss
                           , let ps = [ a ++ ".p~" ++ show i | ((a,i),(_,_,k)) <- (as `zip` is) `zip` xs, k > 1 ]
                           ]
                    | (f ::- xs :-> y,fs) <- table
                    , let as  = [ "a" ++ show i | i <- [1..length xs] ]
                          as' = concat [ [ a ++ "." ++ show i | i <- [0..k-1] ] | (a,(_,k,_)) <- as `zip` xs ]
                          iss = pars [ k | (_,_,k) <- xs ]
                          
                          pars []     = [[]]
                          pars (k:ks) = [ i:is | is <- pars ks, i <- [0..k-1] ]
                          
                          showType xs (y,_,_) = concat [ x ++ " -> " | (x,_,_) <- xs ] ++ y
                    ]
              return (unlines ds)

     return (getDefs, lin)

--------------------------------------------------------------------------------

main = runH mainH

mainH =
  do io $ putStrLn ("-- Found " ++ show (length ws) ++ " words.")
     io $ putStrLn "-- Creating grammar..."
     (showGr, lin) <- newGrammar ws funs
     io $ putStrLn "-- Adding sentences..."
     sequence_
       [ do io $ putStrLn s
            ([vs'],_) <- lin t
            vs' =: vs
       | (t,s) <- table
       , let vs = lex s
       ]
     io $ putStrLn "-- Solving..."
     check
     s <- showGr
     io $ putStr s
 where
  ws = nub [ w | (_, s) <- table, w <- lex s ]

  --lex = words
  --lex = words . concatMap (\c -> if c == '-' then "- " else [c])
  
  lex = map article . words . concatMap (\c -> if c == '-' then "- " else [c])
   where
    article w | last w == '-' = "[il-]"
              | otherwise     = w


{-
  table =
    [ (mkS sg (mkNP det red girl) bful,     "het rode meisje is mooi")
    , (mkS sg (mkNP det bful girl) red,     "het mooie meisje is rood")
    , (mkS sg (mkNP det happy boy) red,     "de blije jongen is rood")
    , (mkS sg (mkNP det red boy) happy,     "de rode jongen is blij")
    , (mkS sg (mkNP det red house) bful,    "het rode huis is mooi")
    , (mkS sg (mkNP det happy house) red,   "het blije huis is rood")
    , (mkS pl (mkNP det red girl) bful,     "de rode meisjes zijn mooi")
    , (mkS pl (mkNP det bful girl) red,     "de mooie meisjes zijn rood")
    , (mkS pl (mkNP det happy boy) red,     "de blije jongens zijn rood")
    , (mkS pl (mkNP det happy house) red,   "de blije huizen zijn rood")
    , (mkS sg (mkNP det happy chair) red,   "de blije stoel is rood")
    , (mkS pl (mkNP det red chair) bful,    "de rode stoelen zijn mooi")
    , (mkS sg (mkNP indet red boy) bful,    "een rode jongen is mooi")
    , (mkS sg (mkNP indet happy chair) red, "een blije stoel is rood")
    , (mkS pl (mkNP indet red girl) bful,   "rode meisjes zijn mooi")
    , (mkS pl (mkNP indet bful house) red,  "mooie huizen zijn rood")
    , (mkS sg (mkNP indet bful girl) happy, "een mooi meisje is blij")
    ]
-}

  table =
    [ (mkS sg (mkNP det red girl) bful,     "it-tifla l-ħamra hija sabiħa")
    , (mkS sg (mkNP det bful girl) red,     "it-tifla s-sabiħa hija ħamra")
    , (mkS sg (mkNP det happy boy) red,     "it-tifel il-ferrieħi huwa aħmar")
    , (mkS sg (mkNP det red boy) happy,     "it-tifel l-aħmar huwa ferrieħi")
    , (mkS sg (mkNP det red house) bful,    "id-dar il-ħamra hija sabiħa")
    , (mkS sg (mkNP det happy house) red,   "id-dar il-ferriħija hija ħamra")
    , (mkS pl (mkNP det red girl) bful,     "it-tfajliet il-ħomor huma sbieħ")
    , (mkS pl (mkNP det bful girl) red,     "it-tfajliet l-isbieħ huma ħomor")
    , (mkS pl (mkNP det happy boy) red,     "is-subien il-ferriħin huma ħomor")
    , (mkS pl (mkNP det happy house) red,   "id-djar il-ferriħin huma ħomor")
    , (mkS sg (mkNP det happy chair) red,   "is-siġġu l-ferrieħi huwa aħmar")
    , (mkS pl (mkNP det red chair) bful,    "is-siġġijiet l-ħomor huma sbieħ")
    , (mkS sg (mkNP indet red boy) bful,    "tifel aħmar huwa sabiħ") -- no good translation of indets
    , (mkS sg (mkNP indet happy chair) red, "siġġu ferrieħi huwa aħmar")
    , (mkS pl (mkNP indet red girl) bful,   "tfajliet ħomor huma sbieħ")
    , (mkS pl (mkNP indet bful house) red,  "djar sbieħ huma ħomor")
    , (mkS sg (mkNP indet bful girl) happy, "tifla sabiħa hija ferriħija")
    
    -- added by Inari
    , (mkS sg (mkNP indet bful boy) happy, "tifel sabiħ huwa ferrieħi")
    ]

--------------------------------------------------------------------------------

type Cat = (String, Int, Int)

data Typ = [Cat] :-> Cat
 deriving ( Eq, Ord, Show )

data Fun = String ::- Typ
 deriving ( Eq, Ord, Show )

arity :: Fun -> Int
arity (_ ::- xs :-> _) = sum [ k | (_,k,_) <- xs ]

rarity :: Fun -> Int
rarity (_ ::- _ :-> (_, rar, _)) = rar

funSize :: Fun -> Int
funSize f@(_ ::- xs :-> (_, rar, _)) = rar * product [ p | (_, _, p) <- xs ]

data Tree = App Fun [Tree]
 deriving ( Eq, Ord, Show )

s    = ("S",    1, 1)
numb = ("Numb", 0, 2)
np   = ("NP",   2, 3)
art  = ("Art",  0, 2)
noun = ("Noun", 2, 2)
adj  = ("Adj",  4, 1)

funs = [ (fmkS, 3), (fmkNP, 4) ] ++ [ (w, 1) | w <- dict ]
 where
  dict =
    [ fsg, fpl
    , fdet, findet
    , fbful, fhappy, fred
    , fhouse, fgirl, fboy, fchair
    ]

verb = ("Verb", 1, 1)

fmkS   = "mkS"   ::- [numb, np, adj] :-> s
fmkNP  = "mkNP"  ::- [art, adj, noun] :-> np
fbe    = "be"    ::- [] :-> verb
fsg    = "sg"    ::- [] :-> numb
fpl    = "pl"    ::- [] :-> numb
fdet   = "det"   ::- [] :-> art
findet = "indet" ::- [] :-> art
fbful  = "bful"  ::- [] :-> adj
fhappy = "happy" ::- [] :-> adj
fred   = "red"   ::- [] :-> adj
fhouse = "house" ::- [] :-> noun
fgirl  = "girl"  ::- [] :-> noun
fboy   = "boy"   ::- [] :-> noun
fchair = "chair" ::- [] :-> noun

mkS numb np adj   = App fmkS [numb,np,adj]
mkNP det adj noun = App fmkNP [det,adj,noun]

be = App fbe []

sg = App fsg []
pl = App fpl []

det   = App fdet []
indet = App findet []

bful  = App fbful []
happy = App fhappy []
red   = App fred []

house = App fhouse []
girl  = App fgirl []
boy   = App fboy []
chair = App fchair []

