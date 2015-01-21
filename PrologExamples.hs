{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, MultiParamTypeClasses, FlexibleInstances, RankNTypes #-}
module Main where

import Prolog
import Data.List ( intersperse )

--------------------------------------------------------------------------------

main = main2

--------------------------------------------------------------------------------

class Display a where
  display :: a -> H String

instance Display () where
  display _ = return "()"

instance (Display a, Display b) => Display (a,b) where
  display (x,y) = do a <- display x
                     b <- display y
                     return ("(" ++ a ++ "," ++ b ++ ")")

instance Show a => Display (Val a) where
  display v = return (concat (intersperse "|" (map show (domain v))))

disp :: Display a => a -> H ()
disp x = do s <- display x; io $ putStrLn s

--------------------------------------------------------------------------------

newtype List a = List (Thunk (Data L (a, List a)))
 deriving ( Constructive, Equal )
data L = Nil | Cons
 deriving ( Eq, Ord, Show )

nil       = List (con Nil unr)
cons x xs = List (con Cons (x, xs))

isNil  (List xs) h = isCon Nil  xs $ \_ -> h
isCons (List xs) h = isCon Cons xs $ \(a,as) -> h a as

instance ConstructiveData L where
  constrs = [Nil, Cons]

instance Equal a => EqualData L (a, List a) where
  equalData h =
    [ ([Cons], \(x,_)  (y,_)  -> h x y)
    , ([Cons], \(_,xs) (_,ys) -> h xs ys)
    ]

instance Value a => Value (List a) where
  type Type (List a) = [Type a]
  
  dflt _ = []

  get (List t) = getData f [] t
   where
    f Nil  _ = return []
    f Cons a = do (x,xs) <- get a; return (x:xs)

instance Display a => Display (List a) where
  display (List th) = 
    do ml <- peek th
       case ml of
         Nothing -> return "_"
         Just (Con c ~(x,xs)) ->
           case cs of
             [Nil] -> return "[]"
             _     -> do a <- display x
                         as <- displayRest xs
                         return ("[" ++ (if Nil `elem` cs then "}" else "") ++ a ++ as)
          where
           cs = domain c
   where
    displayRest (List th) = 
      do ml <- peek th
         case ml of
           Nothing -> return "/_"
           Just (Con c ~(x,xs)) ->
             case cs of
               [Nil] -> return "]"
               _     -> do a <- display x
                           as <- displayRest xs
                           return ((if Nil `elem` cs then "}" else "") ++ "," ++ a ++ as)
            where
             cs = domain c

--------------------------------------------------------------------------------

newtype Nat = Nat (Thunk (Data N Nat))
 deriving ( Constructive, Equal )
data N = Zero | Succ
 deriving ( Eq, Ord, Show )

nat 0 = Nat (con Zero unr)
nat i = Nat (con Succ (nat (i-1)))

suc n = Nat (con Succ n)

isZero (Nat n) h = isCon Zero n $ \_ -> h
isSucc (Nat n) h = isCon Succ n $ \n' -> h n'

instance ConstructiveData N where
  constrs = [Zero, Succ]

instance EqualData N Nat where
  equalData h = [([Succ], \t1 t2 -> postpone $ h t1 t2)]

instance Value Nat where
  type Type Nat = Integer
  
  dflt _ = 0

  get (Nat t) = getData f 0 t
   where
    f Zero _ = return 0
    f Succ a = do n <- get a; return (n+1)

instance Display Nat where
  display (Nat th) = 
    do mn <- peek th
       case mn of
         Nothing -> return "_"
         Just d  -> do (i,j,b) <- info d
                       return (show i ++ (if j > i then "-" ++ show j else "")
                                      ++ (if b then "+" else ""))
   where
    info (Con c ~(Nat th)) =
      case cs of
        [Zero] -> do return (0,0,False)
        _      -> do (i,j,b) <- infoTh th
                     return (if Zero `elem` cs then 0 else i+1,j+1,b)
     where
      cs = domain c
    
    infoTh th =
      do md <- peek th
         case md of
           Nothing -> return (0,0,True)
           Just d  -> info d

--------------------------------------------------------------------------------

app xs ys zs =
  choice
  [ isNil xs $
      equalHere ys zs

  , isCons xs $ \a as ->
      isCons zs $ \b bs ->
        do equalHere a b
           postpone $ app as ys bs
  ]
            
add x y z =
  choice
  [ isZero x $
      equalHere y z

  , isSucc x $ \a ->
      isSucc z $ \c ->
        postpone $ add a y c
  ]
            
--------------------------------------------------------------------------------

newtype RE a = RE (Thunk (Data R (a, (RE a, RE a))))
 deriving ( Constructive, Equal )
data R = RNil | REps | RAtom | RPlus | RAnd | RSeq | RStar
 deriving ( Eq, Ord, Show )

rnil      = RE (con RNil unr)
reps      = RE (con REps unr)
ratom a   = RE (con RAtom (a,unr))
rplus p q = RE (con RPlus (unr,(p,q)))
rand  p q = RE (con RAnd  (unr,(p,q)))
rseq  p q = RE (con RSeq  (unr,(p,q)))
rstar p   = RE (con RStar (unr,(p,unr)))

isRNil  (RE r) h = isCon RNil  r $ \_ -> h
isREps  (RE r) h = isCon REps  r $ \_ -> h
isRAtom (RE r) h = isCon RAtom r $ \(a,_) -> h a
isRPlus (RE r) h = isCon RPlus r $ \(_,(p,q)) -> h p q
isRAnd  (RE r) h = isCon RAnd  r $ \(_,(p,q)) -> h p q
isRSeq  (RE r) h = isCon RSeq  r $ \(_,(p,q)) -> h p q
isRStar (RE r) h = isCon RStar r $ \(_,(p,_)) -> h p

instance ConstructiveData R where
  constrs = [RNil, REps, RAtom, RPlus, RAnd, RSeq, RStar]

instance Equal a => EqualData R (a, (RE a, RE a)) where
  equalData h =
    [ ([RAtom],                 \(x,_)     (y,_)     -> h x y)
    , ([RPlus,RAnd,RSeq,RStar], \(_,(p,_)) (_,(q,_)) -> postpone $ h p q)
    , ([RPlus,RAnd,RSeq],       \(_,(_,p)) (_,(_,q)) -> postpone $ h p q)
    ]

data EXP a = NIL | EPS | ATOM a | EXP a :+: EXP a | EXP a :&: EXP a | EXP a :>: EXP a | STAR (EXP a) deriving ( Show )

instance Value a => Value (RE a) where
  type Type (RE a) = EXP (Type a)
  
  dflt _ = NIL

  get (RE t) = getData f NIL t
   where
    f RNil  _         = return NIL
    f REps  _         = return EPS
    f RAtom (x,_)     = do a <- get x; return (ATOM a)
    f RPlus (_,pq)    = do (x,y) <- get pq; return (x :+: y)
    f RAnd  (_,pq)    = do (x,y) <- get pq; return (x :&: y)
    f RSeq  (_,pq)    = do (x,y) <- get pq; return (x :>: y)
    f RStar (_,(p,_)) = do x <- get p; return (STAR x)

instance Display a => Display (RE a) where
  display (RE th) =
    do md <- peek th
       case md of
         Nothing -> return "_"
         Just (Con c ~(x,~(p,q))) ->
           do x0 <- sequence
                    [ return "e"
                    | REps `elem` cs
                    ]
              x1 <- sequence
                    [ return "#"
                    | RNil `elem` cs
                    ]
              x2 <- sequence
                    [ display x
                    | RAtom `elem` cs
                    ]
              x3 <- sequence
                    [ do a <- display p
                         b <- if any (`elem` cs) [RPlus, RSeq, RAnd] then
                                display q
                               else
                                return ""
                         return (a ++ "`" ++ concat (intersperse "|" ops) ++ "`" ++ b)                                 
                    | any (`elem` cs) [RStar, RPlus, RSeq, RAnd]
                    , let ops = [ op | c <- cs, (c1,op) <- opers, c1 == c ]
                          opers = [ (RStar, "*"), (RPlus, "+"), (RAnd, "&"), (RSeq, ";") ]
                    ]
              return ("(" ++ concat (intersperse "|" (concat [x0,x1,x2,x3])) ++ ")")
          where
           cs = domain c

rec r s =
  do rec1 <- new
     p1 <- new
     s1 <- new
     inContext rec1 $ postponeReal $ rec p1 s1
     sames1 <- new
     inContext sames1 $ equalHere s1 s
     
     rec2 <- new
     p2 <- new
     s2 <- new
     inContext rec2 $ postponeReal $ rec p2 s2
     sames2 <- new
     inContext sames2 $ equalHere s2 s
  
     choice
       [ isREps r $
           isNil s $
             do addClauseHere [nt rec1]
                addClauseHere [nt rec2]
                addClauseHere [nt sames1]
                addClauseHere [nt sames2]
       
       , isRAtom r $ \a ->
           isCons s $ \b bs ->
             isNil bs $
               do addClauseHere [nt rec1]
                  addClauseHere [nt rec2]
                  addClauseHere [nt sames1]
                  addClauseHere [nt sames2]
                  equalHere a b
       
       , isRPlus r $ \p q ->
           choice
           [ do addClauseHere [rec1]
                addClauseHere [nt rec2]
                equalHere p p1
                addClauseHere [sames1]
                addClauseHere [nt sames2]
           , do addClauseHere [nt rec1]
                addClauseHere [rec2]
                equalHere q p2
                addClauseHere [nt sames1]
                addClauseHere [sames2]
           ]
 
       , isRAnd r $ \p q ->
           do addClauseHere [rec1]
              equalHere p p1
              addClauseHere [sames1]
              addClauseHere [rec2]
              equalHere q p2
              addClauseHere [sames2]
       
       , isRSeq r $ \p q ->
           do addClauseHere [rec1]
              addClauseHere [rec2]
              app s1 s2 s
              equalHere p p1
              equalHere q p2
              addClauseHere [nt sames1]
              addClauseHere [nt sames2]
       
       , isRStar r $ \p ->
           choice
           [ isNil s $ 
               do addClauseHere [nt rec1]
                  addClauseHere [nt rec2]
                  addClauseHere [nt sames1]
                  addClauseHere [nt sames2]
           
           , isCons s1 $ \_ _ ->
               do addClauseHere [rec1]
                  addClauseHere [rec2]
                  app s1 s2 s
                  equalHere p p1
                  equalHere r p2
                  addClauseHere [nt sames1]
                  addClauseHere [nt sames2]
           ]
       ]

step p a r =
  do rec1 <- new
     p1 <- new
     r1 <- new
     inContext rec1 $ postponeReal $ step p1 a r1
     
     rec2 <- new
     p2 <- new
     r2 <- new
     inContext rec2 $ postponeReal $ step p2 a r2
  
     choice
       [ isRNil p $
           do addClauseHere [nt rec1]
              addClauseHere [nt rec2]
              isRNil r $
                return ()

       , isREps p $
           do addClauseHere [nt rec1]
              addClauseHere [nt rec2]
              isRNil r $
                return ()
       
       , isRAtom p $ \b ->
           do addClauseHere [nt rec1]
              addClauseHere [nt rec2]
              choice
                [ do equalHere a b
                     isREps r $
                       return ()
                , do notEqualHere a b
                     isRNil r $
                       return ()
                ]

       , isRPlus p $ \q1 q2 ->
           do addClauseHere [rec1]
              addClauseHere [rec2]
              equalHere q1 p1
              equalHere q2 p2
              isRPlus r $ \w1 w2 ->
                do equalHere r1 w1
                   equalHere r2 w2
       
       , isRAnd p $ \q1 q2 ->
           do addClauseHere [rec1]
              addClauseHere [rec2]
              equalHere q1 p1
              equalHere q2 p2
              isRAnd r $ \w1 w2 ->
                do equalHere r1 w1
                   equalHere r2 w2
       
       , isRSeq p $ \q1 q2 ->
           do addClauseHere [rec1]
              addClauseHere [rec2]
              equalHere q1 p1
              equalHere q2 p2
              b <- new
              eps q1 b
              choice
                [ do addClauseHere [nt b]
                     isRSeq r $ \w1 w2 ->
                       do equalHere r1 w1
                          equalHere q2 w2
                
                , do addClauseHere [b]
                     isRPlus r $ \w1 w2 ->
                       isRSeq w1 $ \v1 v2 ->
                         do equalHere r1 v1
                            equalHere q2 v2
                            equalHere r2 w2
                ]

       , isRStar p $ \q ->
           do addClauseHere [rec1]
              addClauseHere [nt rec2]
              equalHere q p1
              isRSeq r $ \w1 w2 ->
                do equalHere r1 w1
                   equalHere p w2
       ]

eps p b =
  do rec1 <- new
     p1 <- new
     b1 <- new
     inContext rec1 $ postponeReal $ eps p1 b1
     
     rec2 <- new
     p2 <- new
     b2 <- new
     inContext rec2 $ postponeReal $ eps p2 b2
  
     choice
       [ isRNil p $
           do addClauseHere [nt rec1]
              addClauseHere [nt rec2]
              addClauseHere [nt b]

       , isREps p $
           do addClauseHere [nt rec1]
              addClauseHere [nt rec2]
              addClauseHere [b]
       
       , isRAtom p $ \_ ->
           do addClauseHere [nt rec1]
              addClauseHere [nt rec2]
              addClauseHere [nt b]

       , isRPlus p $ \q1 q2 ->
           do addClauseHere [rec1]
              addClauseHere [rec2]
              equalHere q1 p1
              equalHere q2 p2
              addClauseHere [b1, b2, nt b]
              addClauseHere [nt b1, b]
              addClauseHere [nt b2, b]

       , isRAnd p $ \q1 q2 ->
           do addClauseHere [rec1]
              addClauseHere [rec2]
              equalHere q1 p1
              equalHere q2 p2
              addClauseHere [nt b1, nt b2, b]
              addClauseHere [b1, nt b]
              addClauseHere [b2, nt b]

       , isRSeq p $ \q1 q2 ->
           do addClauseHere [rec1]
              addClauseHere [rec2]
              equalHere q1 p1
              equalHere q2 p2
              addClauseHere [nt b1, nt b2, b]
              addClauseHere [b1, nt b]
              addClauseHere [b2, nt b]

       , isRStar p $ \q ->
           do addClauseHere [nt rec1]
              addClauseHere [nt rec2]
              addClauseHere [b]
       ]

rec2 p s b =
  choice
  [ isNil s $
      eps p b
  
  , isCons s $ \a s' ->
      do q <- new
         step p a q
         postpone $ rec2 q s' b
  ]

size r n =
  do rec1 <- new
     p1 <- new
     n1 <- new
     inContext rec1 $ postponeReal $ size p1 n1
     
     rec2 <- new
     p2 <- new
     n2 <- new
     inContext rec2 $ postponeReal $ size p2 n2
  
     choice
       [ isRNil r $
           isSucc n $ \n' ->
             isZero n' $
             do addClauseHere [nt rec1]
                addClauseHere [nt rec2]
       
       , isREps r $
           isSucc n $ \n' ->
             isZero n' $
             do addClauseHere [nt rec1]
                addClauseHere [nt rec2]
       
       , isRAtom r $ \a ->
           isSucc n $ \n' ->
             isZero n' $
             do addClauseHere [nt rec1]
                addClauseHere [nt rec2]

       , isRPlus r $ \p q ->
           isSucc n $ \n' ->
           do addClauseHere [rec1]
              addClauseHere [rec2]
              equalHere p p1
              equalHere q p2
              add n1 n2 n'
       
       , isRAnd r $ \p q ->
           isSucc n $ \n' ->
           do addClauseHere [rec1]
              addClauseHere [rec2]
              equalHere p p1
              equalHere q p2
              add n1 n2 n'
       
       , isRSeq r $ \p q ->
           isSucc n $ \n' ->
           do addClauseHere [rec1]
              addClauseHere [rec2]
              equalHere p p1
              equalHere q p2
              add n1 n2 n'
       
       , isRStar r $ \p ->
           isSucc n $ \n' ->
             do addClauseHere [rec1]
                addClauseHere [nt rec2]
                equalHere p p1
                equalHere n1 n'
       ]

newtype CHAR = CHAR (Val Char)
 deriving ( Equal, Display )

instance Value CHAR where
  type Type CHAR = Char
  
  dflt _ = '?'
  
  get (CHAR v) = get v

instance Constructive CHAR where
  new = CHAR `fmap` newVal "ABC"

main1 = run $
  do p <- new :: H (RE Nat)
     size p (nat 7)
          
     rec p (cons (nat 0) (cons (nat 1) (cons (nat 2) nil)))
     rec p (cons (nat 0) (cons (nat 0) (cons (nat 1) (cons (nat 2) (cons (nat 2) nil)))))
     rec p (cons (nat 1) (cons (nat 0) (cons (nat 1) (cons (nat 2) (cons (nat 2) nil)))))
     rec p (cons (nat 0) (cons (nat 1) (cons (nat 1) (cons (nat 2) (cons (nat 2) nil)))))
  
     let see = p
     io $ putStrLn "Solving..."
     b <- solve
     io $ print b
     if b then
       do get see >>= (io . print)
      else
       do return ()

newRE 0 =
  do c <- newVal [REps, RNil, RAtom]
     a <- new
     return (RE (This (Con c (a,unr))))

newRE d =
  do c <- newVal constrs
     a <- new
     p <- newRE (d-1)
     q <- newRE (d-1)
     return (RE (This (Con c (a,(p,q)))))

main2 = run $
  do p <- new :: H (RE CHAR)
     q <- new :: H (RE CHAR)
     s <- new :: H (List CHAR)
     --a <- new
     --b <- new
     --let s = cons a (cons b nil)

     --rec2 (p `rseq` q) s ff
     --rec2 (q `rseq` p) s tt
     
     --rec2 (rstar p `rseq` rstar q) s ff
     --rec2 (rstar (p `rplus` q)) s tt
     --rec (rstar (p `rplus` q)) s
     eps p ff
     rec2 (p `rand` (p `rseq` p)) s tt
     
     
     let callb =
           do disp p
              disp q
              disp s
     
     let see = ((p,q),s)
     io $ putStrLn "Solving..."
     b <- solve' callb
     io $ print b
     if b then
       do get see >>= (io . print)
      else
       do return ()

