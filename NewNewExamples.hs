{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, MultiParamTypeClasses, FlexibleInstances, RankNTypes #-}
module Main where

import NewNew
import Data.List ( intersperse )

--------------------------------------------------------------------------------

newtype List a = List (Thunk (Data L (Maybe (a, List a))))
 deriving ( Constructive, Equal )

data L = Nil | Cons
 deriving ( Eq, Ord, Show )

nil       = List (con Nil Nothing)
cons x xs = List (con Cons (Just (x, xs)))

caseList (List xs) h = ifForce xs h
makeList (List xs) h = do a <- force xs; h a

instance ConstructiveData L where
  constrs = [Nil, Cons]

instance Equal a => EqualData L (Maybe (a, List a)) where
  equalData h =
    [ ([Cons], \(Just (x,_))  (Just (y,_))  -> h x y)
    , ([Cons], \(Just (_,xs)) (Just (_,ys)) -> h xs ys)
    ]

instance Value a => Value (List a) where
  type Type (List a) = [Type a]
  
  dflt _ = []

  get (List t) = getData f [] t
   where
    f Nil  _        = return []
    f Cons (Just a) = do (x,xs) <- get a; return (x:xs)

--------------------------------------------------------------------------------

app xs ys zs =
  caseList xs $ \(Con cxs axs) ->
    choice
    [ must (cxs =? Nil) $
        equalHere ys zs

    , must (cxs =? Cons) $
        proj axs $ \(a,as) ->
          makeList zs $ \(Con czs azs) ->
            must (czs =? Cons) $
              proj azs $ \(c,cs) ->
                do equalHere a c
                   app as ys cs
    ]

--------------------------------------------------------------------------------

newtype Nat = Nat (Thunk (Data N (Maybe Nat)))
 deriving ( Constructive, Equal )

data N = Zero | Succ
 deriving ( Eq, Ord, Show )

zer   = Nat (con Zero Nothing)
suc n = Nat (con Succ (Just n))

nat 0 = zer
nat n = suc (nat (n-1))

caseNat (Nat n) h = ifForce n h
makeNat (Nat n) h = do x <- force n; h x

instance ConstructiveData N where
  constrs = [Zero, Succ]

instance EqualData N (Maybe Nat) where
  equalData h = [([Succ], \(Just t1) (Just t2) -> h t1 t2)]

instance Value Nat where
  type Type Nat = Integer
  
  dflt _ = 0

  get (Nat t) = getData f 0 t
   where
    f Zero _        = return 0
    f Succ (Just a) = do n <- get a; return (n+1)

--------------------------------------------------------------------------------

add x y z =
  caseNat x $ \(Con cx ax) ->
    choice
    [ must (cx =? Zero) $
        equalHere y z
    
    , must (cx =? Succ) $
        proj ax $ \a ->
          makeNat z $ \(Con cz az) ->
            must (cz =? Succ) $
              proj az $ \c ->
                add a y c
    ]

--------------------------------------------------------------------------------

newtype RE a = RE (Thunk (Data R (Maybe a, (Maybe (RE a), (Maybe (RE a), ())))))
 deriving ( Constructive, Equal )
 
data R = RNil | REps | RAtom | RPlus | RAnd | RSeq | RStar
 deriving ( Eq, Ord, Show )

rnil      = RE (con RNil (Nothing, (Nothing, (Nothing, ()))))
reps      = RE (con REps (Nothing, (Nothing, (Nothing, ()))))
ratom a   = RE (con RAtom (Just a, (Nothing, (Nothing, ()))))
rplus p q = RE (con RPlus (Nothing, (Just p, (Just q, ()))))
rand  p q = RE (con RAnd  (Nothing, (Just p, (Just q, ()))))
rseq  p q = RE (con RSeq  (Nothing, (Just p, (Just q, ()))))
rstar p   = RE (con RStar (Nothing, (Just p, (Nothing, ()))))

caseRE (RE r) h = ifForce r h
makeRE (RE r) h = force r >>= h

instance ConstructiveData R where
  constrs = [RNil, REps, RAtom, RPlus, RAnd, RSeq, RStar]

instance Equal a => EqualData R (Maybe a, (Maybe (RE a), (Maybe (RE a), ()))) where
  equalData h =
    [ ([RAtom],                 \(Just x,_)         (Just y,_)         -> h x y)
    , ([RPlus,RAnd,RSeq,RStar], \(_,(Just p,_))     (_,(Just q,_))     -> h p q)
    , ([RPlus,RAnd,RSeq],       \(_,(_,(Just p,_))) (_,(_,(Just q,_))) -> h p q)
    ]

data EXP a = NIL | EPS | ATOM a | EXP a :+: EXP a | EXP a :&: EXP a | EXP a :>: EXP a | STAR (EXP a) deriving ( Show )

instance Value a => Value (RE a) where
  type Type (RE a) = EXP (Type a)
  
  dflt _ = NIL

  get (RE t) = getData f NIL t
   where
    f RNil  _         = return NIL
    f REps  _         = return EPS
    f RAtom (Just x,_) = do a <- get x; return (ATOM a)
    f RPlus (_,pq)    = do (x,y) <- get' pq; return (x :+: y)
    f RAnd  (_,pq)    = do (x,y) <- get' pq; return (x :&: y)
    f RSeq  (_,pq)    = do (x,y) <- get' pq; return (x :>: y)
    f RStar (_,(Just p,_)) = do x <- get p; return (STAR x)

    get' (Just p, (Just q, _)) = get (p,q)

--------------------------------------------------------------------------------

step p a r =
  caseRE p $ \(Con cp ap) ->
    do c <- context
     
       rec1 <- new
       r1 <- new
       inContext rec1 $
         do addClauseHere [c]
            proj2 ap $ \p' -> step p' a r1
     
       rec2 <- new
       r2 <- new
       inContext rec2 $
         do addClauseHere [c]
            proj3 ap $ \q' -> step q' a r2
     
       choice
         [ must (cp =? RNil) $
             do addClauseHere [nt rec1]
                addClauseHere [nt rec2]
                makeRE r $ \(Con cr ar) ->
                  must (cr =? RNil) $
                    return ()

         , must (cp =? REps) $
             do addClauseHere [nt rec1]
                addClauseHere [nt rec2]
                makeRE r $ \(Con cr ar) ->
                  must (cr =? RNil) $
                    return ()
         
         , must (cp =? RAtom) $
             proj1 ap $ \b ->
               do addClauseHere [nt rec1]
                  addClauseHere [nt rec2]
                  choice
                    [ do equalHere a b
                         makeRE r $ \(Con cr ar) ->
                           must (cr =? REps) $
                             return ()
                    , do notEqualHere a b
                         makeRE r $ \(Con cr ar) ->
                           must (cr =? RNil) $
                             return ()
                    ]

         , must (cp =? RPlus) $
             do addClauseHere [rec1]
                addClauseHere [rec2]
                makeRE r $ \(Con cr ar) ->
                  must (cr =? RPlus) $
                    proj2 ar $ \w1 ->
                      proj3 ar $ \w2 ->
                        do equalHere r1 w1
                           equalHere r2 w2
         
         , must (cp =? RAnd) $
             do addClauseHere [rec1]
                addClauseHere [rec2]
                makeRE r $ \(Con cr ar) ->
                  must (cr =? RAnd) $
                    proj2 ar $ \w1 ->
                      proj3 ar $ \w2 ->
                        do equalHere r1 w1
                           equalHere r2 w2
         
         , must (cp =? RSeq) $
            proj2 ap $ \p1 ->
            proj3 ap $ \p2 ->
             do addClauseHere [rec1]
                addClauseHere [rec2]
                b <- new
                eps p1 b
                choice
                  [ do addClauseHere [nt b]
                       makeRE r $ \(Con cr ar) ->
                         must (cr =? RSeq) $
                           proj2 ar $ \w1 ->
                             proj3 ar $ \w2 ->
                               do equalHere r1 w1
                                  equalHere p2 w2
                  
                  , do addClauseHere [b]
                       makeRE r $ \(Con cr ar) ->
                         must (cr =? RPlus) $
                           proj2 ar $ \w1 ->
                             proj3 ar $ \w2 ->
                               makeRE w1 $ \(Con cw1 aw1) ->
                                 must (cw1 =? RSeq) $
                                   proj2 aw1 $ \v1 ->
                                     proj3 aw1 $ \v2 ->
                                       do equalHere r1 v1
                                          equalHere p2 v2
                                          equalHere r2 w2
                  ]

         , must (cp =? RStar) $
             do addClauseHere [rec1]
                addClauseHere [nt rec2]
                makeRE r $ \(Con cr ar) ->
                  must (cr =? RSeq) $
                    proj2 ar $ \w1 ->
                      proj3 ar $ \w2 ->
                        do equalHere r1 w1
                           equalHere p w2
         ]

eps p b =
  caseRE p $ \(Con cp ap) ->
    do c <- context
     
       rec1 <- new
       r1 <- new
       inContext rec1 $
         do addClauseHere [c]
            proj2 ap $ \p' -> eps p' r1
     
       rec2 <- new
       r2 <- new
       inContext rec2 $
         do addClauseHere [c]
            proj3 ap $ \q' -> eps q' r2
     
       choice
         [ must (cp =? RNil) $
             do addClauseHere [nt rec1]
                addClauseHere [nt rec2]
                addClauseHere [nt b]

         , must (cp =? REps) $
             do addClauseHere [nt rec1]
                addClauseHere [nt rec2]
                addClauseHere [b]
         
         , must (cp =? RAtom) $
             do addClauseHere [nt rec1]
                addClauseHere [nt rec2]
                addClauseHere [nt b]

         , must (cp =? RPlus) $
             do addClauseHere [rec1]
                addClauseHere [rec2]
                addClauseHere [nt b, r1, r2]
                addClauseHere [nt r1, b]
                addClauseHere [nt r2, b]
         
         , must (cp =? RAnd) $
             do addClauseHere [rec1]
                addClauseHere [rec2]
                addClauseHere [b, nt r1, nt r2]
                addClauseHere [r1, nt b]
                addClauseHere [r2, nt b]
         
         , must (cp =? RSeq) $
             do addClauseHere [rec1]
                addClauseHere [rec2]
                addClauseHere [b, nt r1, nt r2]
                addClauseHere [r1, nt b]
                addClauseHere [r2, nt b]

         , must (cp =? RStar) $
             do addClauseHere [rec1]
                addClauseHere [nt rec2]
                addClauseHere [b]
         ]

rec p s b =
  caseList s $ \(Con cs as) ->
    choice
    [ must (cs =? Nil) $
        eps p b
  
    , must (cs =? Cons) $
        proj as $ \(a,s') ->
          do q <- new
             step p a q
             rec q s' b
    ]

newtype CHAR = CHAR (Val Char)
 deriving ( Equal )

instance Value CHAR where
  type Type CHAR = Char
  
  dflt _ = '?'
  
  get (CHAR v) = get v

instance Constructive CHAR where
  newPoint _ = CHAR `fmap` newVal "ABC"

main = run $
  do p <- newInput :: H (RE CHAR)
     q <- newInput :: H (RE CHAR)
     s <- newInput :: H (List CHAR)
     --a <- new
     --b <- new
     --let s = cons a (cons b nil)

     --rec2 (p `rseq` q) s ff
     --rec2 (q `rseq` p) s tt
     
     --let p = ratom (CHAR (val 'A'))
     --let q = ratom (CHAR (val 'B'))
     
     b <- new
     rec (rstar p `rseq` rstar q) s b
     rec (rstar (p `rplus` q)) s (nt b)
     --rec2 (rstar p `rseq` rstar q) s ff
     --rec2 (rstar (p `rplus` q)) s tt
     --rec (rstar (p `rplus` q)) s
     --eps p ff
     --rec (p `rand` (p `rseq` p)) s tt
     
     
     let see = ((p,q),s)
     io $ putStrLn "Solving..."
     b <- solve
     io $ print b
     if b then
       do get see >>= (io . print)
      else
       do return ()

