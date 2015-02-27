%-----------------------------------------------------------------------------
%
%               Template for sigplanconf LaTeX Class
%
% Name:         sigplanconf-template.tex
%
% Purpose:      A template for sigplanconf.cls, which is a LaTeX 2e class
%               file for SIGPLAN conference proceedings.
%
% Guide:        Refer to "Author's Guide to the ACM SIGPLAN Class,"
%               sigplanconf-guide.pdf
%
% Author:       Paul C. Anagnostopoulos
%               Windfall Software
%               978 371-2316
%               paul@windfall.com
%
% Created:      15 February 2005
%
%-----------------------------------------------------------------------------


\documentclass{sigplanconf}
%include polycode.fmt

% The following \documentclass options may be useful:

% preprint      Remove this option only once the paper is in final form.
% 10pt          To set in 10-point type instead of 9-point.
% 11pt          To set in 11-point type instead of 9-point.
% authoryear    To obtain author/year citation style instead of numeric.

\usepackage{amsmath}
\usepackage{graphicx}

\newcommand{\comment}[1]{\emph{COMMENT: #1}}
\newcommand{\ifthenelse}{|if|-|then|-|else|}

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\conferenceinfo{ICFP '15}{September, 2015, Vancouver, Canada} 
\copyrightyear{2015} 
\copyrightdata{978-1-nnnn-nnnn-n/yy/mm} 
\doi{nnnnnnn.nnnnnnn}

% Uncomment one of the following two, if you are not going for the 
% traditional copyright transfer agreement.

%\exclusivelicense                % ACM gets exclusive license to publish, 
                                  % you retain copyright

%\permissiontopublish             % ACM gets nonexclusive license to publish
                                  % (paid open-access papers, 
                                  % short abstracts)

\titlebanner{DRAFT}        % These are ignored unless
\preprintfooter{}   % 'preprint' option specified.

\title{SAT-based Bounded Model Checking\\of Functional Programs}
\subtitle{}

\authorinfo{Koen Claessen \and Dan Ros{\'e}n}
           {Chalmers University of Technology}
           {\{koen,danr\}@@chalmers.se}

\maketitle

\begin{abstract}
We present a new symbolic evaluation method for functional programs that generates input to a SAT-solver. The result is a bounded model checking method for functional programs that can find concrete inputs that cause the program to produce certain outputs, or show the inexistence of such inputs under certain bounds. SAT-solvers have long been used for bounded model checking of hardware and also low-level software. This paper presents the first method for SAT-based bounded model checking for high-level programs containing recursive algebraic datatypes and unlimited recursion. Our method works {\em incrementally}, i.e. it increases bounds on inputs until it finds a solution. We also present a novel optimization 
\end{abstract}

\category{CR-number}{subcategory}{third-level}

% general terms are not compulsory anymore, 
% you may leave them out
%\terms
%bounded model checking, SAT

\keywords
bounded model checking, SAT, symbolic evaluation

% ------------------------------------------------------------------------------

\section{Introduction}

SAT-based Bounded Model Checking for hardware, revolution.

Finding {\em counter examples}, {\em examples}, {\em inverting functions}, for prototype programming, primarily. Also: see Reach paper. Secondarily, for showing their absence.

Bounded Model Checking for C. Difference here: recursive data structures. Doing this by modelling pointers and the heap does not work.

Motivating example: Finding 2 different inputs for which a show function returns the same result.

QuickCheck, need to write generators, cannot find intricate examples where things have to correspond.

SmallCheck, only for very small examples, depth bound. FEAT is not depth bound, still size limit.

Lazy narrowing, (e.g. Lazy SmallCheck, Lindblad, Reach), exploit the lazy structure of programs + backtracking. Still not good enough for combinatorial search. Could be adapted to 

Old text:

Bounded model checking for hardware has been a great success. Idea: find bugs efficiently, and show absence of bugs up to size bound, exploiting efficient search in SAT-solvers.

This paper we want to bring this power to function programming.

Example of use (sorting).

Motivational talk about in what situations to use this: (1) Instead of QuickCheck/SmallCheck. Gain: no complicated generators. (2) Computing inverses in programming / prototype programs. (3) FP as a metalanguage for generating constraints, to solve a problem.

This paper contains the following contributions:

\begin{itemize}
\item We show how to express values of arbitrary datatypes symbolically in a SAT-solver.

\item We show how a program containing recursive functions over datatypes can be symbolically executed, resulting in a SAT-problem.

\item We show how we can battle certain kinds of exponential blow-up that naturally happen in symbolic evaluation, by means of a novel program transformation.

\item We show to perform bounded model checking {\em incrementally} for growing input sizes, by making use of feedback from the SAT-solver.
\end{itemize}

% ------------------------------------------------------------------------------

\section{Main Idea}

\comment{Perhaps this section should be merged with the intro.}

The programming language FL, part of the formal verification system Forte \cite{forte} is an ML-like language with one particular distinghuishing feature: symbolic booleans. FL has a primitive function with the following type\footnote{Throughout the paper, we use Haskell notation for our examples, even though the examples may not actually be written in the Haskell language.}:
\begin{code}
var :: String -> Bool
\end{code}
The idea behind |var| is that it creates a symbolic boolean value with the given name. It is possible to use the normal boolean operators (|(/\)|, |(\/)|, |(not)|, |(==)|, etc.) on these symbolic booleans, and the result is then computed as a normalized boolean formula in terms of the variables created by |var|. The implementation of FL uses BDDs \cite{bdd} for this.

%format BoolSym = "\mathit{Bool}^\dagger"
What happens when we use \ifthenelse{} with these symbolic booleans to choose between, for example, two given lists? This is unfortunately disallowed in FL, and leads to a run-time error. The Haskell library Duct Logic \cite{duct-logic} provided a similar feature to FL, but used the type system to avoid mixing symbolic booleans with regular Haskell values, by making symbolic booleans |BoolSym| a different type from regular |Bool|.

This paper aims to lift this restriction, and allow for all values in the program to be symbolic.
The problem that an expression such as
\begin{code}
if var "a" then [1] else []
\end{code}
presents is that at symbolic evaluation time, we cannot decide what constructor to return. One of our main ideas in this paper is to transform algebraic datatypes with several constructors, such as for example:
\begin{code}
data List a = Nil | Cons a (List a)
\end{code}
into algebraic with one constructor which is the ``superposition state'' of all possible constructors, that contains enough symbolic boolean variables to decide which constructor we actually have, plus a ``superposition'' of all possible arguments. Here is what we could do for lists:
%format ListSym = "\mathit{List}^\dagger"
%format FalseSym = "\mathit{False}^\dagger"
%format TrueSym = "\mathit{True}^\dagger"
\begin{code}
data ListSym a = NilCons BoolSym (Maybe (a, ListSym a))

nil :: ListSym a
nil = NilCons FalseSym Nothing

cons :: a -> ListSym a -> ListSym a
cons x xs = NilCons TrueSym (Just (x, xs))
\end{code}
Here, |Maybe| is the regular Haskell datatype, not the symbolic datatype. A symbolic list is thus always built using the |NilCons| constructor. The first argument (a symbolic bool) indicates which constructor we are using (|False| for |Nil|, |True| for |Cons|), and the second argument contains the arguments to the |Cons| constructor (which are only used in the case when we actually have a |Cons| constructor).

An extra datatype invariant has to be respected. For |ListSym| it is that whenever it is possible for the constructor to be |True|, the second argument cannot be |Nothing|.

What have we gained from this? It is now possible to implement \ifthenelse{} on lists, in terms of \ifthenelse{} on symbolic booleans and list elements. Here is the implementation:
%format c1
%format c2
%format ma1
%format ma2
\begin{code}
if b then NilCons c1 ma1 else NilCons c2 ma2 =
  NilCons  (if b then c1   else c2)
           (if b then ma1  else ma2)
\end{code}
We also need \ifthenelse{} on the regular |Maybe| type, which in a symbolic setting is only used to indicate the presence or absence of constructor arguments:
%format a1
%format a2
\begin{code}
if b then Nothing  else ma2      = ma2
if b then ma1      else Nothing  = ma1
if b then Just a1  else Just a2  =
  Just (if b then a1 else a2)
\end{code}
If one branch does not have arguments, we choose the other side. If both branches have arguments, we choose between them.

How can we do |case|-expressions on these symbolic lists? It turns out having \ifthenelse{} on the result type is enough. If we have a |case|-expression:
\begin{code}
case xs of
  Nil        -> a
  Cons y ys  -> f (y,ys)
\end{code}
we can translate it to work on symbolic lists as follows:
\begin{code}
let NilCons c ma = xs in
  if c then f (fromJust ma) else a
\end{code}
In this way, the user can use boolean variables to create a symbolic input to a program, for example representing all lists up to a particular length, containing elements up to a particular size, and run the program. The output will be another symbolic expression, about which we can ask questions. For example, if we want to do property checking, the output will be a symbolic boolean, and we can ask if it can ever be |FalseSym|.

In the remainder of the paper we will use the main idea described in this section, with a number of changes. Firstly, we are going to use a SAT-solver instead of BDDs. Also, we want to create inputs to the program {\em incrementally}, without deciding up-front how large the inputs should be.
For these reasons, we move from an {\em expression-based} view (using \ifthenelse{}) to a {\em constraint-based} view.

% ------------------------------------------------------------------------------

\section{Generating Constraints}

In this section, we explain how we can translate a program $p$ in a simple functional programming language into a monadic program $p'$ in Haskell, such that when $p'$ is run, it generates constraints in a SAT-solver that correspond to the behavior of $p$.

\subsection{The Constraint monad}

We start by explaining the API of the monad we use to generate constraints. We make use of an abstract type |Prop|, that represents propositional logic formulas. (The type |Prop| plays the same role as the type |BoolSym| above.)
%format /\ = "\wedge"
%format \/ = "\vee"
%format ==> = "\Rightarrow"
%format nt = "\neg"
\begin{code}
type Prop

(/\), (\/), (==>)  :: Prop -> Prop -> Prop
(nt)               :: Prop -> Prop
true, false        :: Prop
\end{code}
Note however that there is no way to create a variable with a given name of type |Prop|. Variable creation happens inside the constraints generating monad |C|, using the function |newVar|:
\begin{code}
type C a
instance Monad C

newVar  :: C Prop
insist  :: Prop -> C ()
when    :: Prop -> C () -> C ()
\end{code}
Once we have created a proposition that we want to state as a constraint on variables that has to hold, we can use the function |insist|.

The |C| monad also provides a way of keeping track of local assumptions, by means of |when|. The expression |when a m| generates all constraints that are generated by |m|, but they will only hold conditionally under |a|. To explain better what |when| does, consider the following equivalences:
%format === = "\Leftrightarrow"
\begin{code}
when a (insist b)  ===  insist (a ==> b)
when a (m >>= k)   ===  when a m >>= (when a . k)
when a (when b m)  ===  when (a /\ b) m
when false m       ===  return ()
\end{code}
These are logical equivalences, i.e.\ the expressions on the left and right hand side may generate syntactically different sets of constraints, but they are logically equivalent.

|C| can be thought of as a reader monad in the condition, a writer monad in the constraints, and a state monad in variable identifiers. In reality, it is implemented on top of a SAT-solver (in our case, we are using MiniSat \cite{minisat}). The function |newVar| simply creates a new variable in the solver, |insist| generates clauses from a given proposition and the environment condition, and |when| conjoins its proposition argument with the current environment condition to generate the environment for its second argument.

\subsection{Finite choice}

In order to help us define the translation from algebraic datatypes to monadic constraint generating code, we introduce the following abstraction. The type |Fin a| represents a symbolic choice between finitely many values of type |a|.
\begin{code}
newtype Fin a = Fin [(Prop,a)]

newFin :: Eq a => [a] -> C (Fin a)
newFin xs = do  ps <- sequence [ newVal | x <- nub xs ]
                insist (exactlyOne ps)
                return (Fin (ps `zip` nub xs))

one :: a -> Fin a
one x = Fin [(true,x)]

is :: Eq a => Fin a -> a -> Prop
Fin pxs `is` x = head ([p | (p,y) <- pxs, x == y] ++ [false])
\end{code}
The function |newFin| creates a suitable number of new variables, uses a proposition function that creates a formula expressing that exactlyOne of its arguments is true, and returns |Fin a| value which relates the values from |xs| to the corresponding propositional variables. The function |one| creates a |Fin a| with only one option. The function |is| selects the proposition belonging to the given value.

\subsection{Incrementality}

Before we show the symbolic encoding of datatypes in the constraint generation setting, we need to introduce one more auxiliary type. Since we are going to create symbolic inputs to programs {\em incrementally}, i.e.\ without knowing on beforehand how large they should be, we introduce the type |Delay|.
\begin{code}
type Delay a

delay  :: C a -> C (Delay a)
done   :: a -> Delay a
force  :: Delay a -> C a
wait   :: Delay a -> (a -> C ()) -> C ()
\end{code}
Using the function |delay|, we can created a delayed computation of type |Delay a|, which will be executed at most once. For convenience, the function |done| also creates a delayed computation, but one which is already done.
Using |force|, we can make a delayed computation happen. Using |wait|, we can make code wait for a delayed computation to happen, and react to it by executing its second argument.

The way |Delay| is implemented is the standard way lazy thunks are implemented in an imperative setting, by using |IORef|s, as follows:
\begin{code}
data Delay a  =  Done a
              |  Delay (IORef (Either (IO ()) a))
\end{code}
Later in this section, we will see how |Delay| is used.

\subsection{Symbolic datatypes}

In the previous section, we saw how we could make an algebraic datatype symbolic by creating one constructor that is the ``superposition'' of all constructors, with arguments (1) a symbolic value indicating which constructor we have, and (2) the union of all possible arguments to the constructors.

In this subsection, we show how to do this in our constraint-based setting, using a different datatype, namely of arithmetic expressions:
\begin{code}
data Expr a  =  Var a
             |  Add (Expr a) (Expr a)
             |  Mul (Expr a) (Expr a)
             |  Neg (Expr a)
\end{code}
The first thing we need to do to create a symbolic version of this datatype
is to make a new datatype representing the choice of constructors:
\begin{code}
data ExprL = Var | Add | Mul | Neg
\end{code}
The second thing we do is to merge all constructor arguments into one symbolic constructor:
%format ExprSym = "\mathit{Expr}^\dagger"
\begin{code}
data ExprC s = Expr (Fin ExprL)  (Maybe a)
                                 (Maybe (ExprSym a))
                                 (Maybe (ExprSym a))
\end{code}
The new constructor |Expr| has one argument of type |Fin ExprL| that indicates (symbolically) which constructor we are using.

Finally, we define the actual type of symbolic expressions, by using the |Delay| type:
\begin{code}
type ExprSym a = Delay (ExprC a)
\end{code}

Say how general datatypes are represented.

\subsection{Case expressions on symbolic datatypes}

\begin{code}
isNil, isCons :: List a -> Prop
isNil   (List c _ _)  = c `is` Nil
isCons  (List c _ _)  = c `is` Cons

selList1 :: List a -> Maybe a
selList1 (List _ mx _) = mx

selList2 :: List a -> Maybe (List a)
selList2 (List _ _ mxs) = mxs
\end{code}

\subsection{Creating symbolic values}

new, overloaded.

\subsection{Copying symbolic values}

equalHere, overloaded.

\subsection{Translating a program into constraints}

Show the syntax of expressions. Assumption: it all terminates.

%format x1
%format xn = "\mathit{x}_n"
%format e1
%format en = "\mathit{e}_n"
%format s1
%format sn = "\mathit{s}_n"
%format K1
%format Kn = "\mathit{K}_n"
\begin{code}
d ::= f x1 ... xn = e
\end{code}

\begin{code}
e ::=  let x = f s1 ... sn in e
    |  case s of
         K1 -> e1
         ...
         Kn -> en
    |  s
\end{code}

\begin{code}
s ::=  K s1 ... sn
    |  sel s
    |  x
\end{code}

Show the basic translation of expressions.

Show the basic translation of functions (returning their result).

\subsection{Memoization}

Memoization is good, and easy.

Show the memoized translation of functions.

\subsection{Symbolic merging of function calls}

Explain what bad things can happen if we do not do this.

Explain the idea as a program transformation. This only works if we are in a lazy language.

Explain what happens in the generated constraints.

\subsection{Dynamic termination checks}

Even if input program terminates, symbolic program may not terminate without dynamic checks.

Show example.

Add 'check'. Describe in words. Exact implementation is shown in the next section.

% ------------------------------------------------------------------------------

\section{Incrementality}

depth sucks. this is what we actually do.

\subsection{The type Incr}

show API for Incr (FKA Thunk).

show how it should be used to do datatypes.

one extra function when doing case analysis.

show how equalHere is defined for Incr.

show how new is defined for Incr. Hey, no depth needed anymore!

\subsection{Solving strategies for problems using Incr}

queue of contexts that are blocking.

assumption conflict, pick the first context. use minimization.

statement and proof of completeness.

\subsection{Dealing with check}

Just add to the queue!

% ------------------------------------------------------------------------------

\section{Examples}

In this section we aim to describe how our system works in practice by
looking at some examples.

\subsection{Generating sorted lists}

Assume that we are given a predicate about unique and sorted lists,
that all elements are pairwise larger than the next:

\begin{code}
usorted  ::  [Nat] -> Bool
usorted (x:y:xs)  =  x < y && usorted (y:xs)
usorted _         =  True
\end{code}

\noindent
Now we can investigate the expansion strategy by asking for |xs|
such that |usorted xs| and |length xs > n|, given some bound |n|.
With |n|, the trace looks like this:

\begin{verbatim}
xs: _
xs: (List__)
xs: (List_(List__))
xs: (List_(List_(List__)))
xs: (List_(List_(List_(List__))))
xs: (List_(List(Nat_)(List_(List__))))
xs: (List_(List(Nat_)(List(Nat_)(List__))))
xs: (List(Nat_)(List(Nat_)(List(Nat_)(List__))))
xs: (List(Nat_)(List(Nat(Nat_))(List(Nat_)(List__))))
xs: (List(Nat_)(List(Nat(Nat_))(List(Nat(Nat_))(List__))))
xs= Cons Z (Cons (S Z) (Cons (S (S Thunk_Nat)) Nil))
\end{verbatim}

All but the last lines describe a partial view of the value.
Delayed values are represented with a @_@, and other values
with their type constructor and the arguments. The
value is first expanded to be sufficiently wide, and
then the natural number elements are. Note that
no values except for the needed ones are evaluated.
We are not always that lucky as we shall see later.

Can also generate reverese and qrev lists, can generate
sorted lists with |sort xs=xs|.... Later we will look at the more difficult
|sort xs=sort ys|. Sorting stuff

\subsubsection{Terminate without example}

Sometimes it can be noticed that there is no counterexample regardless how the
program is expanded.  The simplest property when this happens is perhaps asking
for an |x| such that |x < Z|. The standard definition of |(<)| returns |False|
for any |y < Z|, so there is a contradiction in this context. This is also the
same context that the Thunk in |x| is waiting for, but since this is
unsatisfiable, it will never be expanded.

Let's return to the previous example with asking for an |xs|, such that
|usorted xs| and |length xs > n|, but with  the new constraint that |all (< n)
xs|.  So the list must be sorted, but the upper bounds on the data is only
local: namely that each element should be below |n|. The other constraint is a
lower bound on the data: that it should at least have length |n|.

When executing this, first the |length| constraint forces the program to expand
to make the list at least that long.  Then the |unsorted| predicate will make
sure that all the elements are pairwise ordered. This will make the first
element to be at least |Z|, the one after that at least |S Z| and so un until
the |n|th element. But then we will eventually enter the situation outlined
above and the |n|th element cannot expand any more, and the system terminates
cleanly with saying:

\begin{verbatim}
Contradiction!
No value found.
\end{verbatim}

\noindent
and thus efficiently proving the property (for a specific choice of |n|, not for all |n|.)
So our system can be used with bounds written as boolean predicates, for instance depth.

\subsubsection{Limitations of termination discovery}

Our system is not an inductive prover and will not terminate on

\begin{code}
nub xs = y:y:ys
\end{code}

\noindent
(Note that it does not help even if the element type is finite.)

nor on:

\begin{code}
usorted (rev xs) && all (< n) xs && length xs > n
\end{code}

\noindent
it keeps expanding the tail of the list, hoping for something....

\subsubsection{Discussion about contracts checking a'la Leon}

....

\subsection{Merge sort}

The section discusses some optimisations that can be done
to functions with more that one recursive call.
The topic is this implementation of merge sort:

\begin{code}
msort      :: [Nat] -> [Nat]
msort []   = []
msort [x]  = [x]
msort xs   = merge (msort (evens xs)) (msort (odds xs))

merge :: [Nat] -> [Nat] -> [Nat]
merge []      ys      = ys
merge xs      []      = xs
merge (x:xs)  (y:ys)  | x <= y     = x:merge xs (y:ys)
                      | otherwise  = y:merge (x:xs) ys
\end{code}

Here, |evens, odds :: [Nat] -> [Nat]| picks ut the elements
at the even and the odd positions, respectively. 

%format x_1
%format x_2
%format x_3
%format y_1
%format y_2
%format y_3

Symbolically evaluating merge is expensive since |merge| does two recursive
calls. One observation is that evaluating |merge| from the tuple of arguments
|([x_1, x_2, ...],[y_1, y_2, ...])| will make two calls to the pairs
|([x_1, x_2, ...],[y_2, ...])| and
|([x_2, , ...],[y_1, y_2, ...])|. However, both of these will make the call
to the same symbolic lists |([x_2, ...],[y_2, ...])|. We can
avoid to twice calculate symbolic corresponding to those two merged,
by memoising the function. The second time the merge of these two lists
is requested, the saved symbolic list is instead returned.

Another observation is that the calls in |merge| can be \emph{merged} to make |merge'|:

\begin{code}
merge' :: [Nat] -> [Nat] -> [Nat]
merge' []      ys      = ys
merge' xs      []      = xs
merge' (x:xs)  (y:ys)  = hd : merge' l r
  where (hd,l,r)  | x <= y     = (x, xs, y:ys)
                  | otherwise  = (y, x:xs, ys)
\end{code}

When evaluating the program strict, these versions of merge make no difference,
but when evaluating it symbolically, the |merge'| version will make a
\emph{linear} number of calls instead of \emph{exponential} in the length of
the lists.

Our compiler can make this transformation automatically given that the
user annotates which calls in the program to collapse.

In Figure \ref{inj} the task is, given a length bound |n|, to find |xs|, |ys| of type |[Nat]| subject to:

> xs /= ys && msort xs == msort ys && length xs >= n

The runtime is considerably better for the |merge'| version, and the memoised
version of |merge| is considerably better than the unmemoised version.
The runtimes are compared to Leon and LazySmallCheck. Their 
best runtime was chosen from the |evens|-|odds| version or the more standard
|splitAt (length xs `div` 2)| version of |msort| (both favored the
latter version). It should be said that our system works worse on
that version.  

We also applied the |merge| to |merge'| transformation 
by hand for them, but this did not improve their runtime. 

\begin{figure}[htp] \centering{
\includegraphics[scale=0.60]{inj.pdf}}
\caption{
Run time to find |xs|, |ys :: [Nat]| such that |xs /= ys|
and |msort xs == msort ys| with a constraint on |length xs|.
Our tool is \emph{opt} (using |merge'|), \emph{memo} (using |merge| and memoisation),
\emph{unopt} (using |merge|). The other tools are LazySmallCheck and Leon.
\label{inj}
}
\end{figure}

\subsection{Inverting type checking}

%format :-> = ":\rightarrow"
%format env = "\rho"

\begin{code}
data Expr = App Expr Expr Ty | Lam Expr | Var Nat

data Ty = Ty :-> Ty | A | B | C 

tc :: [Ty] -> Expr -> Ty -> Bool
tc  env  (App f x tx)  t           = tc env f (tx :-> t) 
                                   && tc env x tx
tc  env  (Lam e)       (tx :-> t)  = tc (tx:env) e t
tc  env  (Lam e)       _           = False
tc  env  (Var x)       t           =  case env `index` x of 
                                        Just tx  -> tx == t 
                                        Nothing  -> False
\end{code}

\begin{code}
nf :: Expr -> Bool
nf (App (Lam _) _ _) = False
nf (App f x _)       = nf f && nf x
nf (Lam e)           = nf e
nf (Var _)           = True
\end{code}

> tc [] e ((A :-> B :-> C) :-> (A :-> B) :-> A :-> C)

> nf e && tc [] e ((A :-> B :-> C) :-> (A :-> B) :-> A :-> C)

\subsection{Regular expressions}

%format :+: = ":\!\!+\!\!:"
%format :&: = ":\!\&\!:"
%format :>: = ":>:"

\begin{code}
step  :: R T -> T -> R T
step  (Atom a)   x  = if a == x then Eps else Nil
step  (p :+: q)  x  =  step p x :+:  step q x
step  (p :&: q)  x  =  step p x :&:  step q x
step  (p :>: q)  x  =  (step p x :>: q) :+: 
                       if eps p then step q x else Nil
step  (Star p)   x  =  step p x :>: Star p
step  _          x  = Nil

rec :: R T -> [T] -> Bool
rec p []      = eps p
rec p (x:xs)  = rec (step p x) xs
\end{code}

... smart constructors .....

\begin{code}
eps  :: R T -> Bool
eps  Eps                = True
eps  (p :+: q)          = eps p || eps q
eps  (p :&: q)          = eps p && eps q
eps  (p :>: q)          = eps p && eps q
eps  (Star _)           = True
eps  _                  = False
\end{code}

.. eps .. memo eps

> not (eps p) && rec (p :&: (p :>: p)) s 

\begin{verbatim}
p: (R(R(R__(T))_(T))(R__(T))(T))
s: (List(T)(List(T)(List(T)(List(T)_))))

Counterexample!
p: Star (Atom B) :>: Atom B
s: Cons B (Cons B Nil)
\end{verbatim}

(28s! quicker when either of the constructors are replaced with the smart constructors)

\begin{code}
iter :: Nat -> R T -> R T
iter Z     _ = Eps
iter (S n) r = r :>: iter n r
\end{code}

> i /= j && not (eps p) && rec (iter i p :&: iter j p) s

On this example: 

\begin{verbatim}
i: (Nat(Nat(Nat_)))
j: (Nat(Nat(Nat_)))
p: (R(R(R__(T))_(T))(R__(T))(T))
s: (List(T)(List(T)(List(T)_)))

Counterexample!
i: S (S Z)
j: S Z
p: Star (Atom A) :>: Atom A
s: Cons A (Cons A Nil)
\end{verbatim}

\subsection{Ambiguity detection}

TODO
Showing stuff, inverse.

\subsection{Integration from Differentiation}
Deriving expressions, inverse.

\subsection{Synthesising turing machines}
Turing machines?

% --- %

Also show higher-order functions?

% ------------------------------------------------------------------------------

\section{Experimental evaluations}

\begin{table}[htd]
\begin{center}

\textit{
\begin{tabular}{l r r r }
\em Problem & \em Our tool & \em Lazy SC & \em Leon \\
\hline
\hline
\multicolumn{4}{l}{Sorting} \\
...  & x.xs &  x.xs & x.xs \\
...  & x.xs &  x.xs & x.xs \\
\multicolumn{4}{l}{Inverting type checker} \\
\hline
|(w)|         & 1.0s &  x.xs & x.xs \\
|(.)|         & 6.7s &  x.xs & x.xs \\
|s|           & 7.6s &  x.xs & x.xs \\
|nf|, |w|     & 0.1s &  0.9s & x.xs \\
|nf|, |(.)|   & 0.3s &  x.xs & x.xs \\
|nf|, |s|     & 0.8s &  x.xs & x.xs \\
\multicolumn{4}{l}{Regular expressions} \\
\hline
|p :&: (p :>: p)|        & 27.2s &  0.6s & x.xs \\
|p .&. (p .>. p)|        &  2.0s &  0.4s & x.xs \\
|iter i p :&: iter j p|  &  6.6s & 17.4s & x.xs \\
|iter i p .&. iter j p|  & 12.6s & 18.8s & x.xs \\
\multicolumn{4}{l}{Show} \\
\hline
ambig  & x.xs &  x.xs & x.xs \\
\end{tabular}
}
\end{center}
\caption{Evaluation on the examples}
\label{eval}
\end{table}%

Compare some examples against Leon.

Compare some examples against Lazy SmallCheck.

Compare with/without memoization and with/without merging function calls.

Compare with/without conflict minimization?

Show timings of the above examples.

% ------------------------------------------------------------------------------

\section{Related Work}

Leon.

QuickCheck.

Enumeration (SmallCheck, FEAT).

Lazy narrowing (Lazy SmallCheck, Reach, Lindblad).

% ------------------------------------------------------------------------------

\section{Discussion and Future Work}

Make choices of which constructor arguments to merge less arbitrary.

Make choices of which function calls to merge automatic.

Make choice of what to memoize automatic.

Higher-order functions.

Laziness.

Crashing programs (and respecting laziness).

Targets a la Reach.

Using SMT. Integers (trivial, but how to do recursion over integers that terminates? add check everywhere?). Equality and functions can be used to encode constructor functions, selector functions, function application. This is what Leon does. Gain?

If-then-else vs. new and equalHere.

Using BDDs. Incrementality would not work. But otherwise it is not a bad idea. Should use the if-then-else method. The only variables would be the ones created in the input.

% ------------------------------------------------------------------------------

\section{Conclusions}

This is a hard problem.

We have found a niche, works well (and better than others) for cases where the SAT problem is not too big, and one gains something from combinatorial search power.

Our method does not work well when: (1) Expansion does the wrong thing (in which case you can do this by hand), (2) Expansion is too careful, too many small steps, (3) the SAT-problem becomes too big (all intermediate datastructures are remembered), or (4) the SAT-problem is too hard. 

It is perhaps surprising that this is even possible; coding a search problem over a program containing recursive functions over recursive datastructures in terms of a SAT-problem, which is inherently finite.

% ------------------------------------------------------------------------------

%\appendix
%\section{Appendix Title}


\acks

Acknowledgments, if needed.

% We recommend abbrvnat bibliography style.

\bibliographystyle{abbrvnat}
\bibliography{Paper}

% The bibliography should be embedded for final submission.

%\begin{thebibliography}{}
%\softraggedright

%\bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
%P. Q. Smith, and X. Y. Jones. ...reference text...

%\end{thebibliography}


\end{document}
