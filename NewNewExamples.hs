{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, MultiParamTypeClasses, FlexibleInstances, RankNTypes #-}
module Main where

import NewNew
import Data.List ( intersperse )
import System.IO.Unsafe( unsafePerformIO )
import Data.IORef

--------------------------------------------------------------------------------

newtype List a = List (Thunk (Data L (Maybe (a, List a))))
 deriving ( Constructive, Equal, Eq )

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

statusList :: List a -> H String
statusList (List t) =
  do md <- peek t
     case md of
       Nothing -> return "_"
       Just (Con _ mn) ->
         do s <- mst mn
            return $
              if s == "_" then
                "[]"
              else
                ".:" ++ s
 where
  mst Nothing  = error "nothing" -- return "_"
  mst (Just p) = statusList (snd p)

--------------------------------------------------------------------------------

app xs ys zs =
  caseList xs $ \(Con cxs axs) ->
    do when (cxs =? Nil) $
        equalHere ys zs

       when (cxs =? Cons) $
        proj axs $ \(a,as) ->
          makeList zs $ \(Con czs azs) ->
            must (czs =? Cons) $
              proj azs $ \(c,cs) ->
                do equalHere a c
                   app as ys cs

--------------------------------------------------------------------------------

newtype Nat = Nat (Thunk (Data N (Maybe Nat)))
 deriving ( Constructive, Equal, Eq )

instance Unwrap Nat (Thunk (Data N (Maybe Nat))) where
  unwrap (Nat t) = t

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

statusNat :: Nat -> H String
statusNat (Nat t) =
  do md <- peek t
     case md of
       Nothing -> return "_"
       Just (Con _ mn) ->
         do s <- mst mn
            return $
              if s == "_" then
                "0"
              else
                "S" ++ s
 where
  mst Nothing  = return "_"
  mst (Just p) = statusNat p

--------------------------------------------------------------------------------

add x y z =
  caseNat x $ \(Con cx ax) ->
    do when (cx =? Zero) $
        equalHere y z
    
       when (cx =? Succ) $
           proj ax $ \a ->
             makeNat z $ \(Con cz az) ->
               must (cz =? Succ) $
                 proj az $ \c ->
                   add a y c

leq x y =
  caseNat x $ \(Con cx ax) ->
    do when (cx =? Succ) $
         caseNat y $ \(Con cy ay) ->
           do when (cy =? Zero) $
                addClauseHere []
           
              when (cy =? Succ) $
                proj ax $ \x' ->
                  proj ay $ \y' ->
                    leq x' y'

minn x y z =
  caseNat x $ \(Con cx ax) ->
    do when (cx =? Zero) $
           makeNat z $ \(Con cz az) ->
             must (cz =? Zero) $
               return ()
                   
       when (cx =? Succ) $
           proj ax $ \a ->
             caseNat y $ \(Con cy ay) ->
               do when (cy =? Zero) $
                      makeNat z $ \(Con cz az) ->
                        must (cz =? Zero) $
                          return ()
                              
                  when (cy =? Succ) $
                      proj ay $ \b ->
                        makeNat z $ \(Con cz az) ->
                          must (cz =? Succ) $
                            proj az $ \c ->
                              minn a b c

maxx x y z =
  caseNat x $ \(Con cx ax) ->
    do when (cx =? Zero) $
        equalHere y z
                
       when (cx =? Succ) $
           proj ax $ \a ->
             caseNat y $ \(Con cy ay) ->
               do when (cy =? Zero) $
                    equalHere x z
                           
                  when (cy =? Succ) $
                      proj ay $ \b ->
                        makeNat z $ \(Con cz az) ->
                          must (cz =? Succ) $
                            proj az $ \c ->
                              maxx a b c

--------------------------------------------------------------------------------

newtype RE a = RE (Thunk (Data R (Maybe a, (Maybe (RE a), (Maybe (RE a), ())))))
 deriving ( Constructive, Equal, Eq )
 
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

statusRE :: RE a -> H String
statusRE (RE t) =
  do md <- peek t
     case md of
       Nothing -> return "_"
       Just (Con _ (_, (mp, (mq, _)))) ->
         do s1 <- mst mp
            s2 <- mst mq
            return $
              if s1 == "_" && s2 == "_" then
                "."
              else
                "(" ++ s1 ++ "#" ++ s2 ++ ")"
 where
  mst Nothing  = return "_"
  mst (Just p) = statusRE p

--------------------------------------------------------------------------------

-- {-
{-# NOINLINE record #-}
record :: (Eq a, Equal b, Constructive b) => String -> (a -> b -> H ()) -> (a -> H b, a -> b -> H ())
record tag =
  unsafePerformIO $
    do putStrLn ("Creating table for " ++ tag ++ "...")
       ref <- newIORef []
       return $ \h ->
         let f x =
               do xys <- io $ readIORef ref
                  --io $ putStrLn ("Table size for " ++ tag ++ ": " ++ show (length xys))
                  (c,y) <- case [ (c,y) | (c,x',y) <- xys, x' == x ] of
                             [] ->
                               do y <- new
                                  c <- new
                                  io $ writeIORef ref ((c,x,y):xys)
                                  inContext c $ h x y
                                  return (c,y)
                         
                             (c,y):_ ->
                               do --io $ putStrLn ("Duplicate call: " ++ tag)
                                  return (c,y)
                  
                  addClauseHere [c]
                  return y

             h' x y =
               do y' <- f x
                  equalHere y' y

          in (f,h')

norecord :: Constructive b => String -> (a -> b -> H ()) -> (a -> H b, a -> b -> H ())
norecord tag h = (f, h)
 where
  f x =
    do y <- new
       h x y
       return y
 -- -}

--------------------------------------------------------------------------------

data Call a b =
  Call
  { doit   :: Bit
  , invoke :: a -> b -> H ()
  }

newCall :: (Constructive a, Constructive b, Equal a, Equal b) => (a -> b -> H ()) -> H (Call a b)
newCall h =
  do b <- new
     x <- new
     y <- new
     c <- context
     inContext b $
       do addClauseHere [c]
          h x y
     return $
       Call{ doit   = b
           , invoke = \x' y' -> do equalHere x' x
                                   equalHere y y'
           }

call :: Call a b -> a -> b -> H ()
call cl x y =
  do addClauseHere [doit cl]
     invoke cl x y

nocall :: Call a b -> H ()
nocall cl =
  do addClauseHere [nt (doit cl)]

repf :: Nat -> RE CHAR -> H (RE CHAR)
repf i p = rep_f (i,p)

rep i p r = rep_r (i,p) r

(rep_f, rep_r) =
  norecord "rep" $ \(i,p) r ->
  caseNat i $ \(Con ci ai) ->
    do when (ci =? Zero) $
         equalHere reps r
                
       when (ci =? Succ) $
        proj ai $ \a ->
          makeRE r $ \(Con cr ar) ->
            must (cr =? RSeq) $
              proj2 ar $ \r1 ->
                do equalHere p r1
                   proj3 ar $ \r2 ->
                     rep a p r2

reppf :: Nat -> Nat -> RE CHAR -> H (RE CHAR)
reppf i j p = repp_f ((i,j),p)

repp i j p r = repp_r ((i,j),p) r

(repp_f, repp_r) =
  norecord "repp" $ \((i,j),p) r ->
  caseNat i $ \(Con ci ai) ->
    do repp' <- newCall $ \ri rr ->
                  caseNat j $ \(Con cj aj) ->
                    proj aj $ \j' -> repp ri j' p rr
    
       when (ci =? Zero) $
             caseNat j $ \(Con cj aj) ->
               do when (cj =? Zero) $
                   do nocall repp'
                      equalHere reps r
               
                  when (cj =? Succ) $
                   makeRE r $ \(Con cr ar) ->
                    must (cr =? RPlus) $
                      proj2 ar $ \r1 ->
                        do equalHere reps r1
                           proj3 ar $ \r2' ->
                             makeRE r2' $ \(Con cr2' ar2') ->
                               must (cr2' =? RSeq) $
                                 proj2 ar2' $ \r2 ->
                                   do equalHere p r2
                                      proj3 ar2' $ \r3 ->
                                        do call repp' zer r3
                                           --repp zer j' p r3

       when (ci =? Succ) $
             proj ai $ \a ->
               caseNat j $ \(Con cj aj) ->
                 do when (cj =? Zero) $
                     do nocall repp'
                        equalHere rnil r
                 
                    when (cj =? Succ) $
                     makeRE r $ \(Con cr ar) ->
                       must (cr =? RSeq) $
                         proj2 ar $ \r1 ->
                           do equalHere p r1
                              proj3 ar $ \r2 ->
                                do call repp' a r2
                                   --repp a j' p r2

step p a r =
  step_r (p,a) r

stepf p a =
  step_f (p,a)

(step_f, step_r) =
  norecord "step" $ \(p,a) r ->
  caseRE p $ \(Con cp ap) ->
    do step1 <- newCall $ \() r1 ->
                  proj2 ap $ \p' -> step p' a r1
       step2 <- newCall $ \() r2 ->
                  proj3 ap $ \q' -> step q' a r2
     
       whens [cp =? RNil, cp =? REps] $
             do nocall step1
                nocall step2
                makeRE r $ \(Con cr ar) ->
                  must (cr =? RNil) $
                    return ()

       when (cp =? RAtom) $
             proj1 ap $ \b ->
               do nocall step1
                  nocall step2
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

       whens [cp =? RPlus, cp =? RAnd] $
             do makeRE r $ \(Con cr ar) ->
                  do equalHere cp cr
                     proj2 ar $ \w1 ->
                       proj3 ar $ \w2 ->
                         do call step1 () w1
                            call step2 () w2
         
       when (cp =? RSeq) $
            proj2 ap $ \p1 ->
            proj3 ap $ \p2 ->
             do b <- epsf p1
                when (nt b) $
                       makeRE r $ \(Con cr ar) ->
                         must (cr =? RSeq) $
                           proj2 ar $ \w1 ->
                             proj3 ar $ \w2 ->
                               do call step1 () w1
                                  nocall step2
                                  equalHere p2 w2
                  
                when b $
                       makeRE r $ \(Con cr ar) ->
                         must (cr =? RPlus) $
                           proj2 ar $ \w1 ->
                             proj3 ar $ \w2 ->
                               makeRE w1 $ \(Con cw1 aw1) ->
                                 must (cw1 =? RSeq) $
                                   proj2 aw1 $ \v1 ->
                                     proj3 aw1 $ \v2 ->
                                       do call step1 () v1
                                          equalHere p2 v2
                                          call step2 () w2

       when (cp =? RStar) $
             do nocall step2
                makeRE r $ \(Con cr ar) ->
                  must (cr =? RSeq) $
                    proj2 ar $ \w1 ->
                      proj3 ar $ \w2 ->
                        do call step1 () w1
                           equalHere p w2

{-
  caseRE p $ \(Con cp ap) ->
    do step1 <- newCall $ \() r1 ->
                  proj2 ap $ \p' -> step p' a r1
       step2 <- newCall $ \() r2 ->
                  proj3 ap $ \q' -> step q' a r2
     
       choice
         [ must (cp =? RNil) $
             do nocall step1
                nocall step2
                makeRE r $ \(Con cr ar) ->
                  must (cr =? RNil) $
                    return ()

         , must (cp =? REps) $
             do nocall step1
                nocall step2
                makeRE r $ \(Con cr ar) ->
                  must (cr =? RNil) $
                    return ()
         
         , must (cp =? RAtom) $
             proj1 ap $ \b ->
               do nocall step1
                  nocall step2
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
             do makeRE r $ \(Con cr ar) ->
                  must (cr =? RPlus) $
                    proj2 ar $ \w1 ->
                      proj3 ar $ \w2 ->
                        do call step1 () w1
                           call step2 () w2
         
         , must (cp =? RAnd) $
             do makeRE r $ \(Con cr ar) ->
                  must (cr =? RAnd) $
                    proj2 ar $ \w1 ->
                      proj3 ar $ \w2 ->
                        do call step1 () w1
                           call step2 () w2
         
         , must (cp =? RSeq) $
            proj2 ap $ \p1 ->
            proj3 ap $ \p2 ->
             do b <- new
                eps p1 b
                choice
                  [ do addClauseHere [nt b]
                       makeRE r $ \(Con cr ar) ->
                         must (cr =? RSeq) $
                           proj2 ar $ \w1 ->
                             proj3 ar $ \w2 ->
                               do call step1 () w1
                                  nocall step2
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
                                       do call step1 () v1
                                          equalHere p2 v2
                                          call step2 () w2
                  ]

         , must (cp =? RStar) $
             do nocall step2
                makeRE r $ \(Con cr ar) ->
                  must (cr =? RSeq) $
                    proj2 ar $ \w1 ->
                      proj3 ar $ \w2 ->
                        do call step1 () w1
                           equalHere p w2
         ]
-}

(epsf, eps) =
  record "eps" $ \p b ->
    do s <- statusRE p
       --io $ putStrLn ("eps " ++ s)
       eps' p b
 where
  eps' p b =
    caseRE p $ \(Con cp ap) ->
      do (rand,ror) <- new
      
         rec <- newCall $ \() () ->
                  proj2 ap $ \q1 ->
                    proj3 ap $ \q2 ->
                      do r1 <- epsf q1
                         r2 <- epsf q2
                         addClause [nt ror, nt b, r1, r2]
                         addClause [nt ror, nt r1, b]
                         addClause [nt ror, nt r2, b]
                         addClause [nt rand, b, nt r1, nt r2]
                         addClause [nt rand, r1, nt b]
                         addClause [nt rand, r2, nt b]

         whens [cp =? RNil, cp =? RAtom] $
               do nocall rec
                  addClauseHere [nt b]

         whens [cp =? REps, cp =? RStar] $
               do nocall rec
                  addClauseHere [b]
           
         when (cp =? RPlus) $
               do call rec () ()
                  addClauseHere [ror]
           
         whens [cp =? RAnd, cp =? RSeq] $
               do call rec () ()
                  addClauseHere [rand]

{-
  caseRE p $ \(Con cp ap) ->
    do (r1,r2) <- new
    
       eps1 <- newCall $ \() () ->
                 proj2 ap $ \p' -> eps p' r1
       eps2 <- newCall $ \() () ->
                 proj3 ap $ \p' -> eps p' r2
       
       orr <- new
       addClause [nt orr, nt b, r1, r2]
       addClause [nt orr, nt r1, b]
       addClause [nt orr, nt r2, b]

       andd <- new
       addClause [nt andd, b, nt r1, nt r2]
       addClause [nt andd, r1, nt b]
       addClause [nt andd, r2, nt b]

       choice
         [ must (cp =? RNil) $
             do nocall eps1
                nocall eps2
                addClauseHere [nt b]

         , must (cp =? REps) $
             do nocall eps1
                nocall eps2
                addClauseHere [b]
         
         , must (cp =? RAtom) $
             do nocall eps1
                nocall eps2
                addClauseHere [nt b]

         , must (cp =? RPlus) $
             do call eps1 () ()
                call eps2 () ()
                addClauseHere [orr]
         
         , must (cp =? RAnd) $
             do call eps1 () ()
                call eps2 () ()
                addClauseHere [andd]
         
         , must (cp =? RSeq) $
             do call eps1 () ()
                call eps2 () ()
                addClauseHere [andd]

         , must (cp =? RStar) $
             do nocall eps1
                nocall eps2
                addClauseHere [b]
         ]
-}

recf p s = rec_f (p,s)

rec p s b = rec_r (p,s) b

(rec_f, rec_r) =
  norecord "rec" $ \(p,s) b ->
  caseList s $ \(Con cs as) ->
    do when (cs =? Nil) $
        eps p b
  
       when (cs =? Cons) $
        proj as $ \(a,s') ->
          do q <- stepf p a
             rec q s' b

newtype CHAR = CHAR (Val Char)
 deriving ( Equal, Eq )

instance Value CHAR where
  type Type CHAR = Char
  
  dflt _ = '?'
  
  get (CHAR v) = get v

instance Constructive CHAR where
  newPoint _ = CHAR `fmap` newVal "ABC"



main = run $
  do --a <- new
     --b <- new
     --let s = cons a (cons b nil)

     --rec2 (p `rseq` q) s ff
     --rec2 (q `rseq` p) s tt
     
     --let p = ratom (CHAR (val 'A'))
     --let q = ratom (CHAR (val 'B'))

{- 
     p <- newInput :: H (RE CHAR)
     q <- newInput :: H (RE CHAR)
     s <- newInput :: H (List CHAR)
     b <- new
     eps p tt
     eps q tt
     rec (rstar (p `rplus` q)) s b
     rec (rstar (p `rseq` q)) s (nt b)
     
     let see = ((p,q),s)
         h = return ()
-}     
     --rec2 (rstar p `rseq` rstar q) s ff
     --rec2 (rstar (p `rplus` q)) s tt
     --rec (rstar (p `rplus` q)) s
     --eps p ff
     --rec (p `rand` (p `rseq` p)) s tt

{-
     p <- newInput :: H (RE CHAR)
     s <- newInput :: H (List CHAR)
     i1 <- newInput :: H Nat
     i2 <- newInput :: H Nat
     
     eps p ff
     pi1 <- repf i1 p
     pi2 <- repf i2 p
     notEqualHere i1 i2
     
     rec (pi1 `rand` pi2) s tt

     let see = ((i1,i2),(p,s))
     let h = do io . putStrLn =<< statusNat i1
                io . putStrLn =<< statusNat i2
                io . putStrLn =<< statusRE p
                io . putStrLn =<< statusList s
-}

{-
     p <- newInput :: H (RE CHAR)
     s <- newInput :: H (List CHAR)
     let a = CHAR (val 'A')
         --p = ratom a `rplus` (ratom a `rseq` ratom a)
     
     eps p ff
     --q1 <- new
     --rep (nat 1) p q1
     --q2 <- new
     --rep (nat 2) p q2
     --rec (q1 `rand` q2) s tt

     let see = (p,s)
     let h = do io . putStrLn =<< statusRE p
                io . putStrLn =<< statusList s
-}

{-
     p <- newInput :: H (RE CHAR)
     s <- newInput :: H (List CHAR)
     
     eps p ff
     (i1,j1) <- newInput :: H (Nat, Nat)
     (i2,j2) <- newInput :: H (Nat, Nat)
     
     --let i1 = nat 0
     --let j1 = nat 0
     --let i2 = nat 2
     --let j2 = nat 2
     
     leq i1 (nat 0)
     leq j1 (nat 1)
     leq i2 (nat 2)
     leq j2 (nat 2)
     
     p1 <- reppf i1 j1 p
     p2 <- reppf i2 j2 p
     
     (i,j) <- new
     maxx i1 i2 i
     minn j1 j2 j
     
     p12 <- reppf i j p
     
     b <- new
     rec (p1 `rand` p2) s b
     rec p12 s (nt b)

     let see = (((i1,j1),(i2,j2)),(p,s))
     let h = do io . putStrLn =<< statusNat i1
                io . putStrLn =<< statusNat j1
                io . putStrLn =<< statusNat i2
                io . putStrLn =<< statusNat j2
                io . putStrLn =<< statusRE p
                io . putStrLn =<< statusList s
-}

     io $ putStrLn "Solving..."
     b <- solve' h
     io $ print b
     if b then
       do get see >>= (io . print)
      else
       do return ()

