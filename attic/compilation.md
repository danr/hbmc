
This is constructing:

    x : xs ~> r
  =
    c <- force r  -- + newtype unwrap
    must (c =? Cons) $ do
      proj1 r $ \ y ->
      proj2 r $ \ ys ->
      equalHere x y
      equalHere xs ys

With expressions:

    e1 : e2 ~> r
  =
    c <- force r 
    must (c =? Cons) $ do
      proj1 r $ \ y ->
      proj2 r $ \ ys ->
      e1 ~> y
      e2 ~> ys


What's a good intermediate language for lifting out expensive calls?
Can't we dynamically identify identical calls?...
No...

Just keep lifting them out is probably the right thing

f = case ... 
  K1 ... -> ... f ...
  K2 ... -> ... f ...



Two things to do:

* Prolog translation
* Lifting out common calls 
  (including equality that comes from the prolog translation, eek)

 ... in which order? ...

Is the Prolog translation equivalent to just making lets?

How do we type/reason about the lifted out common calls before they make sense?
What semantics do these programs have? Some kind of lazy promise thingamajig

    f = case ... 
      K1 ... -> ... f a ...
      K2 ... -> ... f b ...
      K3 ... -> ...
~>

   f = 
     let 
       x = new
       r = new
       u = new
       r = onlyIf u (f x)
     in case ... 
      K1 ... -> ... assign u True (assign x a (r ...))
      K2 ... -> ... assign u True (assign x b (r ...))
      K3 ... -> assign u False (...)

good: only lift out of one case at a time 

    assign :: a -> a -> b -> {- SneakyIO -} b

if all assignments to a variable are the same, just do it

    case
     A -> f a b
     B -> f a c
     C -> t

  =

    let
      x = new
      y = new
      u = new
      r = onlyIf u (f x y)
    in case ...
      A -> u = True ; x = a; y = b; r
      B -> u = True ; x = a; y = c; r
      C -> u = False ; t

   now, x = a in all branches that assign to x, so we get:

    let
      y = new
      u = new
      r = onlyIf u (f a y)
    in case ...
      A -> u = True ; y = b; r
      B -> u = True ; y = c; r
      C -> u = False ; t

    (similarily, if all branches do the recursive call, 
     we get "onlyIf True e" which reduces to "e")

Q: where shoulld the let be? should it be between case and the branches? 
   the variables are only used afterwards
A: if the scrutinee can only be a variable, it does not matter.
   let's have it like that.

Important:

1. After prolog translation, shift case/eval/wait-construct upwards as much as possible
   without shifting past other case/eval/waits.

2. Replace introduced variables in case with projections to find equal calls.

3. Don't dig into other case's branches later.

Then starts the prolog translation. It should be simple enough.

-- example

merge xs0 ys0 = 
  case xs0 of
    x:xs -> 
      case ys0 of
        y:ys ->
          case x < y of
            T -> x : merge xs (y:ys)
            F -> y : merge (x:xs) ys
        [] -> xs0
    [] -> ys0

=>

merge xs0 ys0 = 
  case xs0 of
    x:xs -> 
      case ys0 of
        y:ys ->
          let as = new
              bs = new
              c  = new
              r  = onlyIf c (merge as bs)
          case x < y of
            T -> x : (c = True; as = xs; bs = y:ys; r) 
            F -> y : (c = True; as = x:xs; bs = ys; r)
        [] -> xs0
    [] -> ys0

NOTE: No subterm of the lifted call should be deemed "expensive".
      i.e  f (f x), lift out "f x", not the entire "f (f x)"

law: 
    onlyIf b (let a = new in e) === let a = new in onlyIf b e

now, we have that c is equal to the same thing, namely True, in all
branches, so we lift it out: (but to where?)

merge xs0 ys0 = 
  case xs0 of
    x:xs -> 
      case ys0 of
        y:ys ->
          let as = new
              bs = new
              c  = new
              r  = onlyIf c (merge as bs)
          c = True; case x < y of
            T -> x : (as = xs; bs = y:ys; r) 
            F -> y : (as = x:xs; bs = ys; r)
        [] -> xs0
    [] -> ys0

law:
    let x = new in x = e; b === let x = e in b

law: 
    if x only occurs once in b:

    let x = e in b === b[e/x]


merge xs0 ys0 = 
  case xs0 of
    x:xs -> 
      case ys0 of
        y:ys ->
          let as = new
              bs = new
              r  = onlyIf True (merge as bs)
          case x < y of
            T -> x : (as = xs; bs = y:ys; r) 
            F -> y : (as = x:xs; bs = ys; r)
        [] -> xs0
    [] -> ys0

law:
    onlyIf True e = e

merge xs0 ys0 = 
  case xs0 of
    x:xs -> 
      case ys0 of
        y:ys ->
          let as = new
              bs = new
              r  = merge as bs
          case x < y of
            T -> x : (as = xs; bs = y:ys; r) 
            F -> y : (as = x:xs; bs = ys; r)
        [] -> xs0
    [] -> ys0

Actually, we don't case on x lt y:

merge xs0 ys0 = 
  case xs0 of
    x:xs -> 
      case ys0 of
        y:ys ->
          let lt = x < y
          case lt of
            T -> x : merge xs (y:ys)
            F -> y : merge (x:xs) ys
        [] -> xs0
    [] -> ys0

but then the case already has a prenex... should we start before it or after it?

after it, because if it contains a function that we want to lift out, we cannot anyway
lift it out. also we might want the variables in scope.

with this in mind, perhaps the earlier passes can seem more monolithic
(that they will start from the beginning, find the appropriate case to work on,
lift out, then simplify, and so on)

when hosting an exrpession out must we then also hoist out the let-bindings 
it recursively depends on:

    case x of
        A -> let y = e1 in f e2
        B -> f e3
        C -> K

=>

    let a = new
        b = new
        r = onlyIf b (f a)
    case x of 
        A -> let y = e1 in (b = True; a = e2; r)
        B -> b = True; a = e3; r
        C -> b = False; K

Seems like: no!

But what about equality assignments that are in the way?

