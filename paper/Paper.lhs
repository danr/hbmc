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
\usepackage{xcolor}
\usepackage{graphicx}
\usepackage{textcomp}

\newcommand{\comment}[1]{\emph{COMMENT: #1}}
\newcommand{\ifthenelse}{|if|-|then|-|else|}
%format § = $

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
We present a new symbolic evaluation method for functional programs that generates input to a SAT-solver. The result is a bounded model checking method for functional programs that can find concrete inputs that cause the program to produce certain outputs, or show the inexistence of such inputs under certain bounds. SAT-solvers have long been used for bounded model checking of hardware and low-level software. This paper presents the first method for SAT-based bounded model checking for high-level programs containing recursive algebraic datatypes and unlimited recursion. Our method works {\em incrementally}, i.e. it increases bounds on inputs until it finds a solution. We also present a novel optimization, namely {\em function call merging}, that can greatly reduce the complexity of symbolic evaluation for recursive functions over datatypes with multiple recursive constructors.
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
\item We present a monad for constraint generation that can be used to generate constraints for a SAT-solver.

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

\comment{explain the limitations of static input size / depth, and how we want things to be: a completely free input that is ``expanded'' by the solver, completely automatically}

In the remainder of the paper we will use the main idea described in this section, with a number of changes. Firstly, we are going to use a SAT-solver instead of BDDs. Also, we want to create inputs to the program {\em incrementally}, without deciding up-front how large the inputs should be.
For these reasons, we move from an {\em expression-based} view (using \ifthenelse{}) to a {\em constraint-based} view.

% ------------------------------------------------------------------------------

\section{A DSL for generating constraints}

In this section, we present a small DSL, the constraint monad, that we will use later for generating constraints to a SAT-solver. We also show how it can be used to encode algebraic datatypes symbolically.

\subsection{The Constraint monad}

We start by explaining the API of the monad we use to generate constraints. We make use of an abstract type |Prop|, that represents propositional logic formulas. (The type |Prop| plays the same role as the type |BoolSym| above.)
%format /\ = "\wedge"
%format \/ = "\vee"
%format ==> = "\Rightarrow"
%format <=> = "\Leftrightarrow"
%format nt = "\neg"
\begin{code}
type Prop

(/\), (\/), (==>), (<=>)  :: Prop -> Prop -> Prop
(nt)                      :: Prop -> Prop
true, false               :: Prop
\end{code}
Note however that there is no way to create a variable with a given name of type |Prop|. Variable creation happens inside the constraints generating monad |C|, using the function |newVar|:
\begin{code}
type C a
instance Monad C

newVar  :: C Prop
insist  :: Prop -> C ()
when    :: Prop -> C () -> C ()
\end{code}
We can use the function |insist| to state that a given proposition has to hold. In this way, we generate constraints.

The function |when| provides a way of keeping track of local assumptions. The expression |when a m| generates all constraints that are generated by |m|, but they will only hold conditionally under |a|. To explain better what |when| does, consider the following equivalences:
%format === = "\Longleftrightarrow"
\begin{code}
when a (insist b)  ===  insist (a ==> b)
when a (m >>= k)   ===  when a m >>= (when a . k)
when a (when b m)  ===  when (a /\ b) m
when false m       ===  return ()
\end{code}
These are logical equivalences, i.e.\ the expressions on the left and right hand side may generate syntactically different sets of constraints, but they are logically equivalent.

|C| can be thought of as a reader monad in the environment condition (hereafter called the {\em context}), a writer monad in the constraints, and a state monad in variable identifiers. In reality, it is implemented on top of a SAT-solver (in our case, we are using MiniSat \cite{minisat}). The function |newVar| simply creates a new variable in the solver, |insist| generates clauses from a given proposition and the environment condition, and |when| conjoins its proposition argument with the current environment condition to generate the environment for its second argument.

\subsection{Finite choice}

In order to help us define the translation from algebraic datatypes to monadic constraint generating code, we introduce the following abstraction. The type |Fin a| represents a symbolic choice between finitely many concrete values of type |a|.
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
The function |newFin| creates a suitable number of new variables, uses a proposition function |exactlyOne| that creates a formula expressing that exactly one of its arguments is true, and returns |Fin a| value which relates the values from |xs| to the corresponding propositional variables. The function |one| creates a |Fin a| with only one option. The function |is| selects the proposition belonging to the given value.

\subsection{Incrementality}

Before we show the symbolic encoding of datatypes in the constraint generation setting, we need to introduce one more auxiliary type. Since we are going to create symbolic inputs to programs {\em incrementally}, i.e.\ without knowing on beforehand how large they should be, we introduce the type |Delay|\footnote{As we shall see in Section \ref{sec:solving}, the story is slightly more complicated than this, but we present a simplified version here for presentation purposes.}.
\begin{code}
type Delay a

delay  :: C a -> C (Delay a)
done   :: a -> Delay a
force  :: Delay a -> C a
wait   :: Delay a -> (a -> C ()) -> C ()
\end{code}
Using the function |delay|, we can created a delayed computation of type |Delay a|, which will be executed at most once. For convenience, the function |done| also creates a delayed computation, but one which is already done.
Using |force|, we can make a delayed computation happen. Using |wait|, we can make code wait for a delayed computation to happen, and react to it by executing its second argument.

The way |Delay| is implemented is the standard way lazy thunks are implemented in an imperative setting, using |IORef|s, as follows:
\begin{code}
data Delay a  =  Done a
              |  Delay (IORef (Either (C ()) a))
\end{code}
A |Delay| is either an already evaluated value, or a mutable reference filled with either a constraint generator that, when run, will fill the reference with a value, or a value.

In order to use references in the |C|-monad, we lift the standard |IORef| functions into the |C|-monad:
\begin{code}
newRef    :: a -> C (IORef a)
readRef   :: IORef a -> C a
writeRef  :: IORef a -> a -> C ()
\end{code}
In Section \ref{sec:inputs}, a more detailed implementation of |Delay|s is given. In the next subsection, we will see how |Delay| is used.

\subsection{Symbolic datatypes}

In the previous section, we saw how we could make an algebraic datatype symbolic by creating one constructor that is the ``superposition'' of all constructors, with arguments (1) a symbolic value indicating which constructor we have, and (2) the union of all possible arguments to the constructors.

In this subsection, we show how to do this in our constraint-based setting, by example, and using a different datatype, namely of arithmetic expressions:
\begin{code}
data Expr a  =  Var a
             |  Add (Expr a) (Expr a)
             |  Mul (Expr a) (Expr a)
             |  Neg (Expr a)
\end{code}
The first thing we need to do to create a symbolic version of this datatype
is to make a new datatype representing the choice of constructors:
\begin{code}
data ExprL = Var | Add | Mul | Neg deriving ( Eq )
\end{code}
The second thing we do is to merge all constructor arguments into one symbolic constructor:
%format ExprSym = "\mathit{Expr}^\dagger"
\begin{code}
data Arg a    = X | An a

data ExprC s  = Expr (Fin ExprL)  (Arg a)
                                  (Arg (ExprSym a))
                                  (Arg (ExprSym a))
\end{code}
The new constructor |Expr| has one argument of type |Fin ExprL| that indicates (symbolically) which constructor we are using. The other arguments are the (multi-set) union of all arguments that are used by any of the original constructors. We use the type |Arg|, which is isomorphic to the Haskell |Maybe| type to indicate that some arguments may not always be present.
In the merged constructor |Expr|, we reuse argument positions as much as possible; for example the first arguments of |Add|, |Mul|, and |Minus| are all represented by one argument of the symbolic |Expr| constructor.

We are assuming a datatype invariant that guarantees that an |Arg| argument is not |X| when it is possible that the constructor argument 

Finally, we define the actual type of symbolic expressions, by using the |Delay| type:
\begin{code}
type ExprSym a = Delay (ExprC a)
\end{code}
A symbolic expression is thus an object that can potentially create a choice of constructors, plus the choice of arguments, which in turn can be symbolic expressions again.

All recursive types have to use the |Delay| constructor, because in general we cannot know in advance what the size is. With |Delay|, we can delay this decision until later, when we see what happens when we evaluate the program.

For convenience, we create the following helper functions that represent the old constructor functions:
\begin{code}
var       :: a -> ExprSym a
add, mul  :: ExprSym a -> ExprSym a -> ExprSym a
neg       :: ExprSym a -> ExprSym a

var x    = done (Expr (one Var) (An a)  X       X)
add a b  = done (Expr (one Add) X       (An a)  (An b))
mul a b  = done (Expr (one Add) X       (An a)  (An b))
neg a    = done (Expr (one Neg) X       (An a)  X)
\end{code}
%format TypeSym = "\mathit{Type}^\dagger"
In general, to make a symbolic version of an algebraic datatype |Type|, we create three new types: |TypeL|, which enumerates all constructor functions from |Type|; |TypeC|, which has one argument |Fin TypeL| and moreover the union of all constructor arguments tagged with |Arg|, and |TypeSym|, which is just |Delay TypeC|. Note that this construction also works for mutally recursive datatypes.

We have seen how to construct concrete values in these symbolic datatypes. What is left is to show how to do case analysis on symbolic datatypes, how to construct symbolic values, and how to state equality between . This is presented in the next two subsections.

\subsection{Case expressions on symbolic datatypes}

In a regular case analysis, three things happen: (1) the scrutinee is evaluated, (2) the constructor is examined to make a choice between branches, and (3) the arguments of the constructor are bound in the correct branch.

On symbolic datatypes, we split case analysis in three parts as well. However, our case analysis is {\em passive}; it does not demand any evaluation, instead it will wait until another part of the program defines the scrutinee, and then generate constraints.

To examine which constructor we have, we introduce the following helper functions:
\begin{code}
isVar, isAdd, isMul, isNeg :: ExprC a -> Prop
isVar  (Expr c _ _ _)  = c `is` Var
isAdd  (Expr c _ _ _)  = c `is` Add
isMul  (Expr c _ _ _)  = c `is` Mul
isNeg  (Expr c _ _ _)  = c `is` Neg
\end{code}
And to project out relevant arguments, we use the following projection functions:
%format sel1
%format sel2
%format sel3
\begin{code}
sel1 :: ExprC a -> a
sel2 :: ExprC a -> ExprSym a
sel3 :: ExprC a -> ExprSym a

sel1 (Expr _ (An x) _ _)  = x
sel2 (Expr _ _ (An a) _)  = a
sel3 (Expr _ _ _ (An b))  = b
\end{code}
Note that the $\mathit{sel}_i$ functions are partial; we should not use them when the corresponding arguments do not exist.
Now, to express a case expression of the following form on a symbolic datatype:
%format P1
%format P2
%format P3
%format P4
%format //- = "\!"
\begin{code}
case e of
  Var x    -> P1//-[x]
  Add a b  -> P2//-[a,b]
  Mul a b  -> P3//-[a,b]
  Neg a    -> P4//-[a]
\end{code}
We write the following:
\begin{code}
wait e § \ec ->
  do  when (isVar ec)  §  P1//-[sel1 ec]
      when (isAdd ec)  §  P2//-[sel2 ec,sel3 ec]
      when (isMul ec)  §  P3//-[sel2 ec,sel3 ec]
      when (isNeg ec)  §  P4//-[sel2 ec]
\end{code}
First, we wait for the scrutinee to be defined, then we generate 4 sets of constraints, one for each constructor.

\subsection{Creating symbolic values}

We have seen how we can create concrete symbolic values (using |var|, |add|, |mul|, and |neg|), but not how to create values with symbolic variables in them.

Creating these kinds of values turns out to be so useful that we introduce a type class for them:
\begin{code}
class Symbolic a where
  new :: C a
\end{code}
Here are some instances of types we have seen before:
\begin{code}
instance Symbolic Prop where
  new = newVal

instance Symbolic a => Symbolic (Arg a) where
  new = An `fmap` new

instance Symbolic a => Symbolic (Delay a) where
  new = delay new
\end{code}
We already know how to generate symbolic |Prop|s. When generating a completely general symbolic |Arg|, it has to exist (it cannot be |X|). Generating a symbolic |Delay| just delays the generation of its contents, which is how we get incrementality. Generating a symbolic tuple means generating symbolic elements.

When we make a new symbolic datatype |TypeSym|, we have to make an instance of |Symbolic| for its constructor type |TypeC|. Here is what it looks like for |ExprC|:
\begin{code}
instance Symbolic a => Symbolic (ExprC a) where
  new =  do  c <- newFin [Var,Add,Mul,Neg]
             liftM3 (Expr c) new new new
\end{code}
With the instance above, we also have |new :: C ExprSym| to our disposal.

\subsection{Copying symbolic values} \label{sec:copy}

The last operation on symbolic types we need is {\em copying}. Copying is needed when we want to generate constraints that define a symbolic value |y| in terms of a given value |x|. Copying is also used a lot, and therefore we introduce a type class:
%format >>> = "\rhd"
\begin{code}
class Copy a where
  (>>>) :: a -> a -> C ()
\end{code}
The expression |x >>> y| copies |x| into |y|; it defines |y| as |x| under the current environment condition.

Here are some instances of types we have seen before:
\begin{code}
instance Copy Prop where
  p >>> q = insist (p <=> q)

instance Eq a => Copy (Fin a) where
  Fin pxs >>> v = sequence_
    [ insist (p ==> (v `is` x)) | (p,x) <- pxs ]

instance Copy a => Copy (Delay a) where
  s >>> t = wait s § \x -> do  y <- force t
                               x >>> y
\end{code}
For |Prop|, copying is just logical equivalence. For finite values |Fin a|, we let the propositions in the left argument imply the corresponding propositions in the right argument. This is enough because all propositions in a |Fin a| are mutually exclusive.

For |Delay a|, we wait until |s| gets defined, and as soon as this happens, we make sure |t| is defined (if it wasn't already), and copy the contents of |s| to the contents of |t|.

At this stage, it may be interesting to look at an example of a combination of |new| and |>>>|. Consider the following two |C|-expressions:
%format ¤ = "\phantom"
%format /// = "\;\;\;"
%format //  = "\;"
\begin{code}
do  y <- new  ///  ===  /// do x >>> z
    x >>> y
    y >>> z   
\end{code}
Both logically mean the same thing, if |y| is not used anywhere else. The left hand side creates a new |y|, copies |x| into |y| and also copies |y| into |z|. The first copy constraint has the effect of always making sure that |y| is logically equivalent to |x| under the current environment condition. As soon as any |Delay| in |x| becomes defined, which may happen after these constraints have been generated, |y| will follow suit. And whenever |y| expands a |Delay|, |z| will follow suit. So the effect of the left hand side is the same as the right hand side.

To enable copying on symbolic datatypes |TypeSym| we need to make an instance for their corresponding |TypeC|. Here is what this looks like for |ExprC|:
%format x1
%format x2
%format b1
%format b2
\begin{code}
instance Copy a => Copy (ExprC a) where
  Expr c1 x1 a1 b1 >>> Expr c2 x2 a2 b2 =
    do  c1 >>> c2
        when (isVar c1)  §  do x1 >>> x2
        when (isAdd c1)  §  do a1 >>> a2; b1 >>> b2
        when (isMul c1)  §  do a1 >>> a2; b1 >>> b2
        when (isNeg c1)  §  do a1 >>> a2
\end{code}
We can see that copying runs the same recursive call to |>>>| multiple times in different branches. However, we should not be calling these branches, because in one general symbolic call to the above function, {\em all} ``branches'' will be executed! This means that the same recursive call will be executed several times, leading to an exponential blow-up. In Section \ref{sec:memo} we will see how to deal with this.

% ------------------------------------------------------------------------------

\section{Translating programs into constraints}

%format pSym = "\mathit{p}^\dagger"
%format ASym = "\mathit{A}^\dagger"
%format BSym = "\mathit{B}^\dagger"
In this section, we explain how we can translate a program |p :: A -> B| in a simple functional programming language into a monadic program |pSym :: ASym -> C BSym| in Haskell, such that when |pSym| is run on symbolic input, it generates constraints in a SAT-solver that correspond to the behavior of |p|.

For now, we assume that the datatypes and programs we deal with are first-order. We also assume that all definitions are total, i.e.\ terminating and non-crashing. We will later have a discussion on how these restrictions can be lifted.

\subsection{The language}

We start by presenting the syntax of the language we translate. This language is very restricted syntactically, but it is easy to see that more expressive languages can be translated into this language.

Function definitions |d| and recursion can only happen on top-level. A program is a sequence of definitions |d|.
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
Expressions are separated into two categories: {\em simple} expressions and regular expressions. Simple expressions are constructor applications, selector functions, or variables. Regular expressions are let-expressions with a function application, case-expressions, or simple expressions.
\begin{code}
s ::=  K s1 ... sn
    |  sel s
    |  x

e ::=  let x = f s1 ... sn in e
    |  case s of
         K1 -> e1
         ...
         Kn -> en
    |  s
\end{code}
Function application can only happen inside a let-definition and only with simple expressions as arguments. Case-expressions can only match on constructors, the program has to use explicit selector functions to project out the arguments. 

As an example, consider the definition of the standard Haskell function |(++)|:
\begin{code}
(++) :: [a] -> [a] -> [a]
[]      ++ ys  = ys
(x:xs)  ++ ys  = x : (xs ++ ys)
\end{code}
In our restricted language, this function definition looks like:
\begin{code}
xs ++ ys = case xs of
             Nil   -> ys
             Cons  -> let vs = sel2 xs ++ ys
                      in Cons (sel1 xs) vs
\end{code}

\subsection{Basic translation}

%format (transr (e)) = "\llbracket" e "\rrbracket\!\!\!\Rightarrow\!\!\!"
%format (trans (e))  = "\llbracket" e "\rrbracket"
The translation revolves around the basic translation for expressions, denoted |transr e r|, where |e| is a (simple or regular) expression, and |r| is a variable. We write |transr e r| for the monadic computation that generate constraints that copy the symbolic value of the expression |e| into the symbolic value |r|.

Given the translation for expressions, the translation for function definitions is:
\begin{code}
trans (f x1 ... xn = e) /// = /// f x1 ... xn = do  y <- new
                                                    transr e y
                                                    return y
\end{code}
To translate a function definition, we generate code that creates a new symbolic value |y|, translates |e| into |y|, and returns |y|.

The translation for simple expressions is simple, because no monadic code needs to be generated; we have pure functions for concrete data constructors and pure functions for selectors.
\begin{code}
transr s r /// = /// s >>> r
\end{code}
We simply copy the value of the simple expression into |r|.

To translate let-expressions, we use the standard monadic transformation:
\begin{code}
transr (let f s1 ... sn in e//) r /// = /// do  x <- f s1 ... sn
                                                transr e r
\end{code}
To translate case-expressions, we use |wait| to wait for the result to become defined, and then generate code for all branches.
%format isK1 = "\mathit{isK}_1"
%format isKn = "\mathit{isK}_n"
\begin{code}
transr (case s of         ///  =  ///  wait s § \cs ->
          K1 -> e1        ///  ¤  ///  ///   do  when (isK1 cs)  §  transr e1 r
          ...             ///  ¤  ///            ...
          Kn -> en //) r  ///  ¤  ///            when (isKn cs)  §  transr en r
\end{code}

\subsection{An translated example}

Applying our translation to this function and using symbolic lists, yields the following code:
%format ++? = ++"\!^\dagger"
%format ==? = =="^\dagger"
\begin{code}
(++?) :: Symbolic a => ListSym a -> ListSym a -> C (ListSym a)
xs ++? ys = do  zs <- new
                wait xs § \cxs ->
                  when (isNil cxs) §
                    do  ys >>> zs
                  when (isCons cxs) §
                    do  vs <- sel2 cxs ++ ys
                        cons (sel1 cxs) vs >>> zs
\end{code}
An example property that we may use to find a counter example to may look like this:
\begin{code}
appendCommutative xs ys =
  do  vs <-  xs ++? ys
      ws <-  ys ++? xs
      b  <-  vs ==? ws
      insist (nt b)
\end{code}
We use the symbolic version |(==?)| of |(==)| that is generated by our translation. When we run the above computation, constraints will be generated that are going to search for inputs |xs| and |ys| such that |xs++ys == ys++xs| is false.

\subsection{Memoization} \label{sec:memo}

When performing symbolic evaluation, it is very common that functions get applied to the same arguments more than once. This is much more so compared to running a program on concrete values. A reason for this is that in symbolic evaluation, {\em all} branches of every case expression are potentially executed. If two or more branches contain a function application with the same arguments (something that is even more likely to happen when using selector functions), a concrete run will only execute one of them, but a symbolic run will execute all of them. A concrete example of this happens in datatype instances of the function |(>>>)| (see Section \ref{sec:copy}).

An easy solution to this problem is to use memoization. We apply memoization in two ways.

First, for translated top-level function calls that return a result, we keep a memo table that remembers to which symbolic arguments a function has been applied. If the given arguments has not been seen yet, a fresh symbolic result value |r| is created using |new|, and the function body |e| is run {\em in a fresh context} |c|. The reason we run |e| in a fresh context is that we may reuse the result |r| from many different future contexts. In order to use the result |r| from any context, we need to make the context |c| true first (by using |insist|). After storing |c| and |r| in |f|'s memo table, we return |r|. If we have already seen the arguments, we simply return the previously computed result, after making sure to imply the context in which it was created.

Translating a definition |f x1 ... xn = e| with memoization on thus yields the following result:
\begin{code}
f x1 ... xn =
  do  mcy <- lookMemo_f x1 ... xn
      case mcy of
          Nothing     -> do  c <- new
                             y <- new
                             storeMemo_f x1 ... xn (c,y)
                             with c § transr e y
                             insist c
                             return y

          Just (c,y)  -> do  insist c
                             return y
\end{code}
The functions |lookMemo_f| and |storeMemo_f| perform lookup and storage in |f|'s memo table, respectively. The function |with| locally sets the context for its second argument.

Second, we also memoize the copy function |(>>>)|. This function is not a function that returns a result, but it generates constraints instead. However, we treat |(>>>)| as if it was a top-level function returning |()|, and memoize it in the same way.

Memoization can have big consequences for the performance of constraint generation and solving, as shown in the experimental evaluation.
We allow memoization to be turned on and off manually for each top-level function. We always memoize |(>>>)| on |Delay|.

\subsection{Symbolic merging of function calls}

Consider the following program:
\begin{code}
f e =  case e of
         Var v    -> v
         Add a b  -> f a
         Mul a b  -> f b
         Neg a    -> f a
\end{code}
In the previous subsection, we explained that all branches of a case expression have to be explored when performing symbolic evaluation. This is obviously bad when there exist identical function calls that occur in multiple branches. But it is also bad when there are multiple branches that contain a call to the same function |f|, even when those calls do not have the same arguments. A run of |f| on concrete values would take linear time in the depth $k$ of the argument expression. A naive symbolic run of |f| would take time proportional to $3^k$! After applying memoization, this is reduced to $2^k$. However, we would like to get as closely to linear in $k$ as possible.

Consider the following transformed version of the above program, after applying standard program transformations.
%format undefined = "\bot"
\begin{code}
f e =  let y = f (  case e of
                      Var v    -> undefined
                      Add a b  -> a
                      Mul a b  -> b
                      Neg a    -> a )
       in  case e of
             Var v    -> v
             Add a b  -> y
             Mul a b  -> y
             Neg a    -> y
\end{code}
This program behaves the same as the original program (at least in a lazy semantics), but now it only makes one recursive call, {\em even when we symbolically evaluate it}. The trick is to share one generalized call to |f| between all 3 places that need to call |f|. We can do this, because those 3 places never really need to call |f| at the same time; for any concrete input, we can only be in one branch at a time. Thus, we have {\em merged} three calls to |f| into one call.

Our translator can generate constraint producing code that applies the same idea as the above program transformation, but directly expressed in constraint generation code. In order for this to happen, the user has to manually annotate calls to |f| with a special labelling construct |@|:
\begin{code}
f e =  case e of
         Var v    -> v
         Add a b  -> (f a)@ 1
         Mul a b  -> (f b)@ 1
         Neg a    -> (f a)@ 1
\end{code}
The generated constraint producing code will look like this:
%format fSym = "\mathit{f}^\dagger"
\begin{code}
fSym e = do  r <- new
             wait e § \ce ->
               do  c <- new
                   x <- new
                   y <- with c § fSym x
                
                   when (isVar ce) §
                     do  sel1 ce >>> r
                   when (isAdd ce) §
                     do  insist c
                         sel2 ce >>> x
                         y >>> r
                   when (isMul ce) §
                     do  insist c
                         sel3 ce >>> x
                         y >>> r
                   when (isNeg ce) §
                     do  insist c
                         sel2 ce >>> x
                         y >>> r
\end{code}
The above function first waits for its argument to be defined, and then creates a fresh context |c| and a fresh input |x|, and then it evaluates |fSym| with the input |x| in the context |c|. Then, the normal part of the case expression progresses, but instead of calling |fSym|, the branches simply use |insist| to make sure the context of the merged call is set, and copy the argument they need into |x|. This guarantees that |y| gets the correct value. An interesting thing to notice is that, because we are generating constraints and not evaluating values, 

Note that in the above code, because |(>>>)| is memoized, the call |y >>> r| only gets performed once although it appears in the code three times, and |sel2 ce >>> x| also gets performed only once although it appears twice.

Our experimental evaluation also shows the importance of merging function calls in case branches. Automatically knowing when and where to apply the labels of function calls that should be merged is future work.

\subsection{Other optimizations}

We perform a few other optimizations in our translation. Two of them are described here.

Not all algebraic datatypes need to use |Delay|. In principle, for any finite type we do not need to use |Delay| because we know the (maximum) size of the elements on beforehand. In our translator, we decided to not use |Delay| for enumeration types (e.g.\ |BoolSym|).

For definitions that consist of a simple expression |s|, we can translate as follows:
\begin{code}
trans (f x1 ... xn = s) /// = /// f x1 ... xn = do  return s
\end{code}
This avoids the creation of an unnecessary helper value using |new|.

% ------------------------------------------------------------------------------

\section{Solving the constraints} \label{sec:solving}

In the previous two sections, we have seen how to generate constraints in the |C| monad, and how to translate functional programs into constraint producing programs. However, we have not talked about how to actually generate symbolic inputs to programs, and how to use the SAT-solver to find solutions to these constraints. In order to do this, we have to make part of the code we have shown so far slightly more complicated.

\subsection{Inputs and internal points} \ref{sec:inputs}

In a symbolic program, there are two kinds of symbolic expressions: inputs and internal points. They are dealt with in two fundamentally different ways. Inputs are expressions that are created outside of the program, and that are controlled by the solver. If the solver determines that a certain input should be made bigger by expanding one of its delays, it can do so, and the program will react to this, by triggering constraint generators that are waiting for these delays to appear. These triggers may in turn define other delays (by using |>>>|), and a cascade of constraint generators will be set in motion. So, inputs are set on the outside, and internal points react to their stimuli.

We would like to make this difference explicit by introducing two functions to create symbolic expressions: one called |new| for internal points, and one called |newInput| for inputs. To implement this, we introduce a new datatype of |Mode|s, with which symbolic expressions can be labelled.
\begin{code}
data Mode = Input | Internal
\end{code}
The most important place where the label should occur is when we create a |Delay|. We make the following changes:
%format mdo = "\mathbf{mdo}"
\begin{code}
data Delay a  =  Done a
              |  Delay Mode (IORef (Either (C ()) a))

delay :: Mode -> C a -> C (Delay a)
delay m c =
  mdo  ref <-  newRef § Left §
                 do  a <- c
                     writeRef ref (Right a)
       return (Delay m ref)
\end{code}
The function |delay| gets an extra |Mode| argument, which indicates what kind of delay we are creating.

Whenever we create any new symbolic value, we need to be explicit about what kind of value we are creating. We therefore change the |Symbolic| class accordingly:
\begin{code}
class Symbolic a where
  newMode :: Mode -> C a

new, newInput :: Symbolic a => C a
new       = newMode Internal
newInput  = newMode Input
\end{code}
The function |new| now always creates internal points, where as the new function |newInput| creates new inputs.

The mode information needs to be propagated through all calls of |newMode|:
\begin{code}
instance Symbolic Prop where
  newMode _ = newVal

instance Symbolic a => Symbolic (Arg a) where
  newMode m = An `fmap` newMode m

instance Symbolic a => Symbolic (Delay a) where
  newMode m = delay m (newMode m)

instance Symbolic a => Symbolic (ExprC a) where
  newMode m =  do  c <- newFin [Var,Add,Mul,Neg]
                   liftM3  (Expr c) (newMode m)
                           (newMode m) (newMode m)
\end{code}
What is now the different between delays that belong to inputs and delays that belong to internal points? Well, if the program decides to do a |wait| on an internal point, then the algorithm that controls the expansion of the input delays does not need to know this. Internal points are only expanded by the program. But if the program decides to do a |wait| on an input delay, the algorithm that controls the expansion needs to know about it, because now this delay is a candidate for expansion later on.

To implement this, we introduce one more function to the |C| monad:
\begin{code}
enqueue :: Delay a -> C ()
\end{code}
We augment |C| to also be a state monad in a queue of pairs of contexts and delays. The function |enqueue| takes a delay and adds it to this queue together with the current context.

The function |enqueue| is called by the function |wait| when it blocks on an input delay:
\begin{code}
wait :: Delay a -> (a -> C ()) -> C ()
wait (Done x)         k = k x
wait d@(Delay m ref)  k =
  do  ecx <- readRef ref
      case ecx of
        Left cx  -> do  c <- ask
                        writeRef ref § Left §
                          do  cx
                              Right x <- readRef ref
                              with c § k x
                        case m of
                          Input     -> enqueue d
                          Internal  -> return ()
        
        Right x  -> do  k x
\end{code}
When a |C| computation terminates and has generated constraints, we can look at the internal queue and see exactly which parts of the inputs (input delays) are requested by which parts of the program (contexts), and in which order this happened.

\subsection{Solving and expanding}

The main loop we use in our solving algorithm works as follows. We start by creating a SAT-solver, and
running the main |C|-computation. This will produce a number of constraints in the SAT-solver. It will also produce a queue $Q$ of pairs of contexts and unexpanded input delays.

We then enter our main loop.

The first step in the loop is to find out whether or not there exists an actual solution to the current constraints. The insight we employ here is that a real solution (i.e.\ one that corresponds to an actual run of the program) cannot enter any of the contexts that are currently in the queue. This is because those contexts all have pending input delays: case expressions that have not been triggered yet. In other words, the constraints belonging to those contexts are not finished yet; there may yet be more to come. So, when looking for a real solution, we ask the SAT-solver to find a solution to all constraints generated so far, under the assumption that all of the contexts that appear in the queue $Q$ are false. If we find a solution, we can from the model produced by the SAT-solver read off the actual values of the input that satisfy the constraints.

If we do not find a solution, it may be because we still had to expand one of the contexts in the queue $Q$. So, we have to pick an element from the queue, for which we are going to expand the corresponding |Delay|. The simplest choice we can make here is just to pick the first element from the queue, expand the delay contained in it, remove all occurrences of that delay in the queue $Q$, and repeat the main loop. If we do this, we get a completely fair expansion, which leads to an algorithm that is both sound and complete. Soundness here means that any found solution actually corresponds to a real run of the program, and completeness means that we are guaranteed to find a solution if there exists one.

But we can do better. The SAT-solver is able to give feedback about our question of finding a solution under the assumption that all contexts in the queue $Q$ are false. When the answer is no, we also get a {\em subset} of the assumptions for which the SAT-solver has discovered that there is no solution (this subset is called the {\em assumption conflict set} \cite{minisat}, or sometimes an {\em unsatisfiable core} \cite{unsat-core}). Typically, the assumption conflict set is much smaller than the original assumption set. An improved expansion strategy picks a context to expand from the assumption conflict set. It turns out that if always we pick the context from the conflict set that is closest to the front of the queue $Q$, then we also get a sound and complete expansion strategy.

Why is this better? There may be lots of contexts that are waiting for an input to be expanded, but the SAT-solver has already seen that there is no reason to expand those contexts, because making those contexts true would violate a precondition for example. The assumption conflict set is a direct way for the solver to tell us: ``If you want to find a solution, you should make one of these propositions true''. We then pick the proposition from that set that leads to the most fair expansion strategy.

To see why this strategy is complete, consider the case where the full constraint set has a solution $s$, but we are not finding it because we are expanding the wrong delays. In that case, there must after a while exist a finite, non-empty set $S$ of delays in $Q$ that should be expanded in order to reach the desired solution, but that are never chosen when we do choose to expand a delay. (If this does not happen, we will find the solution eventually.) The first observation we make is that for every conflict set that is found, at least one element from $S$ must be a part of it. (If not, this would imply that $s$ was not a solution after all.) Since the expansion strategy does not pick points from $S$ to expand, it picks points that lie closer to the front of the queue instead. But it cannot pick such points infinitely often; eventually the points in $S$ must be the ones closest to the head.

In our experimental evaluation we show that this expansion strategy very often defines just the right constructors in the input in order to find the counter example, even for large examples. We thus avoid having to pick a depth-limit up-front, and even avoid reasoning about depth altogether.

\subsection{Dealing with non-termination}
\label{postpone}

So far, we have assumed that all functions terminate. However, it turns out that this restriction is unnecessary; there is a simple trick we can emply to deal with functions that may not terminate: For possibly non-terminating functions, we use a special function |postpone|:
\begin{code}
postpone :: C () -> C ()
postpone m =  do  x <- newInput
                  wait x § \ () -> m
\end{code}
This function takes a constraint generator as an argument, and postpones it for later execution, by simply constructing a new {\em input} to the program, and blocking in that input. The result is that the expansion of the input in the current context now lies in the expansion $Q$, and it is guaranteed that it will be picked some time in the future, if the solver deems the current context part of a promising path to a solution.

For possibly non-terminating functions |f|, |postpone| is used in the following way:
\begin{code}
trans (f x1 ... xn = e) /// = /// f x1 ... xn = do  y <- new
                                                    postpone § transr e y
                                                    return y
\end{code}
The generation of constraints for the body |e| of |f| is postponed until a later time.

It is good that we have postpone; sometimes, even though our input program clearly terminates, the transformed symbolic program may not terminate. This can happen when the static sizes of symbolic arguments to recursive functions do not shrink, whereas they would shrink in any concrete case. An example is the function |merge| after merging recursive function calls, as explained in the experimental evaluation section. The function |postpone| also works in those cases.

Thus, we use |postpone| on any function which is not structurally recursive {\em after} transformation into a symbolic program.

% ------------------------------------------------------------------------------

\section{Examples and Experiments}

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
such that |usorted xs| and |length xs >= n|, given some bound |n|.
Our tool can output a trace showing how the incremental values
has been expanded so far.  With |n=2|, the trace looks like this:

\begin{verbatim}
xs: _
xs: Lst__
xs: Lst_(Lst__)
xs: Lst_(Lst_(Lst__))
xs: Lst_(Lst_(Lst_(Lst__)))
xs: Lst_(Lst(Nat_)(Lst_(Lst__)))
xs: Lst_(Lst(Nat_)(Lst(Nat_)(Lst__)))
xs: Lst(Nat_)(Lst(Nat_)(Lst(Nat_)(Lst__)))
xs: Lst(Nat_)(Lst(Nat(Nat_))(Lst(Nat_)(Lst__)))
xs: Lst(Nat_)(Lst(Nat(Nat_))(Lst(Nat(Nat_))(Lst__)))
xs= [Z,S Z,S (S Thunk_Nat)]
\end{verbatim}

All but the last lines describe a partial view of the value.
Delayed values are represented with a @_@, and other values
with their type constructor and the arguments. The
value @xs@ is first expanded to contain sufficiently many
elements, namely two, and
then the natural numbers starts to be expanded. Note that
in this case only the necessary values are evaluated.
This can in general not be guaranteed.

% Can also generate reverese and qrev lists, can generate
% sorted lists with |sort xs=xs|.... Later we will look at the more difficult
% |sort xs=sort ys|. Sorting stuff

\subsubsection{Terminate without counterexample}

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

% \subsubsection{Limitations of termination discovery}
% 
% Our system is not an inductive prover and will not terminate on
% 
% \begin{code}
% nub xs = y:y:ys
% \end{code}
% 
% \noindent
% (Note that it does not help even if the element type is finite.)
% 
% nor on:
% 
% \begin{code}
% usorted (rev xs) && all (< n) xs && length xs > n
% \end{code}
% 
% \noindent
% it keeps expanding the tail of the list, hoping for something....
% 
% \subsubsection{Discussion about contracts checking a'la Leon}
% 
% ....

\subsection{Merging the calls in merge}
\label{merge}

%format x_1
%format x_2
%format x_3
%format x_n
%format y_1
%format y_2
%format y_3
%format y_m

% The section discusses some optimisations that can be done
% to functions with more that one recursive call.
% The topic is this implementation of merge sort:
%
% \begin{code}
% msort      :: [Nat] -> [Nat]
% msort []   = []
% msort [x]  = [x]
% msort xs   = merge (msort (evens xs)) (msort (odds xs))
% 
% Here, |evens, odds :: [Nat] -> [Nat]| picks ut the elements
% at the even and the odd positions, respectively. 


This example about |merge| aims to highlight how important
merging of function calls can be. We use
this standard definition of |merge| that merges two lists,
returning a sorted list of the inputs are:

\begin{code}
merge :: [Nat] -> [Nat] -> [Nat]
merge []      ys      = ys
merge xs      []      = xs
merge (x:xs)  (y:ys)  | x <= y     = x:merge xs (y:ys)
                      | otherwise  = y:merge (x:xs) ys
\end{code}

Evaluating merge on symbolic lists is expensive since |merge| 
does two recursive calls, leading to an exponential behaviour. 
One first observation
of the situation reveals that evaluating this expression:

> merge [x_1, x_2, ..., x_n] [y_1, y_2, ..., y_m] 

makes these two calls:

> merge [x_1, x_2, ..., x_n]  [y_2, ..., y_m] 
> merge [x_2, , ..., x_n]     [y_1, y_2, ..., y_m] 

However, both of these will make the following call:

> merge [x_2, ..., x_n] [y_2, ..., y_m] 

We can avoid to twice calculate symbolic corresponding to those two merged, by
memoising the function. The second time the merge of these two lists is
requested, the saved symbolic list is instead returned.

Another observation is that the calls in |merge| 
can be symbolically merged to make |merge'|:

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

Our compiler makes this transformation automatically given that the
user annotates which calls in the program to collapse.

We experimentally evaluated the performance of these three versions
(without any optimisations, with memoisation, and with merged calls)
by increasing a length bound |n|, and asking to find |xs|, |ys| satisfying:

> xs /= ys && msort xs == msort ys && length xs >= n

In words: two different lists that are permutations of each other,
via a |msort| function that calls the different versions of |merge|.

The results are in Figure \ref{inj}, and although we can conjecture
that all versions are exponential from it, the merged function is
significantly better: allowing to go up to lists over size 20 within
reasonable time instead of size 10. We hypothesise that this is 
due to the fact that we can move the exponential behaviour to the
SAT solver rather than in the size of the SAT problem.

The memoized version performs slightly better than the unmemoized
one. The SAT problem is here quadratic in size rather than exponential.

We also compare our runtimes to Leon\cite{leon} and LazySmallCheck\cite{lsc}.

% The runtime is considerably better for the |merge'| version, and the memoised
% version of |merge| is considerably better than the unmemoised version.
% The runtimes are compared to Leon and LazySmallCheck.  

% We also applied the |merge| to |merge'| transformation 
% by hand for them, but this did not improve their runtime. 

\begin{figure}[htp] \centering{
\includegraphics[scale=0.60]{inj.pdf}}
\caption{
Run time to find |xs|, |ys| such that |xs /= ys|
and |msort xs == msort ys| with a |length| constraint on |xs|.
We compare our tool with different settings (\emph{merged}, \emph{memo}, \emph{unopt})
as described in Section \ref{merge}. 
and with LazySmallCheck\cite{lsc} and Leon\cite{leon}.
\label{inj}
}
\end{figure}

\subsubsection{Termination of |merge'|}

The original |merge| function is structurally recursive,
but this property is destroyed when symbolically
merging to |merge'|. The symbolic values that are
fed to the recursive calls are not smaller: for instance,
the first one is |if x <= y then xs else x:xs| which 
is as big as the input |x:xs|. We overcome this
introduced non-termination by introducing a |postpone|
as described in Section \ref{postpone}.

\subsection{From type checking to expressions}

%format :-> = ":\rightarrow"
%format env = "\rho"

We will here consider a standard type-checker for 
simply typed lambda calculus. It answers whether 
a given expression has a given type, in an environment:

> tc :: [Type] -> Expr -> Type -> Bool
> tc  env  (App f x tx)  t           = tc env f (tx :-> t) && tc env x tx
> tc  env  (Lam e)       (tx :-> t)  = tc (tx:env) e t
> tc  env  (Lam e)       _           = False
> tc  env  (Var x)       t           =  case env `index` x of 
>                                         Just tx  -> tx == t 
>                                         Nothing  -> False

By now inverting this function, we can use it 
both to infer the type of a given expression,
or even synthesise programs of a given type!
For instance, we can get the S combinator
by asking for an |e| such that:

> tc [] e ((A :-> B :-> C) :-> (A :-> B) :-> A :-> C)

Upon which our tool answers this term, when pretty-printed:

\begin{code}
\x y z -> ((((\v w -> w) z) x) z) (y z)
\end{code}

This takes about 7 seconds, but as can be seen above,
it contains redexes. Interestingly, we can 
avoid getting redexes \emph{and} reduce the search space by
by adding a recursive predicate 
|nf :: Expr -> Bool|
that checks that there is no unreduced
lambda in the expression. Now, we ask
for the same as above, and that |nf e|.
With this modification, finding the s combinator,
in normal form, takes less a fraction of a second. 
Comparison with and without normal form and
with LazySmallCheck can be found in Table \ref{typetable}.

Constraining the data in this way allows 
cutting away big parts of the search space (only normal 
forms). The context where the expression is not in normal
form will become inconsistent due to the predicate,
and no delayed computations are evaluated from inconsistent
contexts. This would not be the case if we up from decided on how
big our symbolic values were. So here we see a direct benefit from 
incrementally expanding the program.

Both the code for the type checker and the
normal form predicate contains calls that 
can be merged in the fashion as the merge
sort. Without merging these calls, finding the a normal 
form of the s comibator takes about a second,
and 30 seconds without the normal form predicate.

\begin{table}[htd]
\begin{center}

\textit{
\begin{tabular}{l r r}
\em Type & \em Our & \em LazySC \\
\hline
|w    ::(a->a->b)->a->b|         & 1.0s &  - \\
|(.)  ::(b->c)->(a->b)->a->c|    & 6.7s &  - \\
|s    ::(a->b->c)->(a->b)->a->c| & 7.6s &  - \\
|w| in normal form   & $<$0.1s &     0.9s \\
|(.)| in normal form   & $<$0.1s &  - \\
|s| in normal form    & 0.1s &  - \\
\end{tabular}
}
\end{center}
\caption{Using the type checker to synthesise
expressions. LazySmallCheck was given a 300s
time limit for each depth 6, 7 and 8, timeout
is denoted with -.
}
\label{typetable}
\end{table}%

% \begin{code}
% data Expr = App Expr Expr Type | Lam Expr | Var Nat
% 
% data Type = Type :-> Type | A | B | C 
% tc  env  (App f x tx)  t           = tc env f (tx :-> t) 
%                                    && tc env x tx
% tc  env  (Lam e)       (tx :-> t)  = tc (tx:env) e t
% tc  env  (Lam e)       _           = False
% tc  env  (Var x)       t           =  case env `index` x of 
%                                         Just tx  -> tx == t 
%                                         Nothing  -> False
% \end{code}
% 
% \begin{code}
% nf :: Expr -> Bool
% nf (App (Lam _) _ _) = False
% nf (App f x _)       = nf f && nf x
% nf (Lam e)           = nf e
% nf (Var _)           = True
% \end{code}

\subsection{Regular expressions}
\label{regexp}

%format :+: = ":\!\!+\!\!:"
%format :&: = ":\!\&\!:"
%format :>: = ":>:"
%format .>. = ".\!>\!\!."

%format Meps = "\epsilon"
%format (repp (p) (i) (j)) = p "\!\{" i "," j "\}"
%format (reppp (p) (i) (j)) = "(" p ")\!\{" i "," j "\}"
%format (maxx (i) (j)) = i "\cap" j
%format (minn (i) (j)) = i "\cup" j
%format Mempset = "\emptyset"

We used an regular expression library
to falsify some plausible looking laws. The library has the following api:

% We will call the main one |prop_repeat|:
% 
% > Meps `notElem` p && s `elem` repp p i j & repp p i' j' ==> s `elem` repp p (maxx i i') (minn j j')
% 
% Here, |repp p i j| means repeat the regular expression |p| from |i| to |j| times. 
% If |i > j|, then this regular expression does not recognize any string.
% Conjunction of regular expressions is denoted by |&|.
% 
% This property is false for |i = 0|, |j = 1|, |i' = j' = 2|, |p = a+aa| and |s = aa|,
% since |reppp (a+aa) (maxx 0 2) (minn 1 2) = reppp (a+aa) 2 1 = Mempset|.


> data RE a  = a :>: a  | a :+: a  | a :&: a 
>            | Star a   | Eps      | Nil       | Atom Token

> step  ::  RE -> Token -> RE 
> eps   ::  RE -> Bool
> rec   ::  RE -> [Token] -> Bool
> rep   ::  RE -> Nat -> Nat -> RE

The |step| function does Brzozowski differentiation, |eps|
answers if the expression contains the empty string, |rec|
answers if the word is recognised, and |rep p i j| 
repeats a regexp from |i| to |j| times. 
If |i > j|, then this regular expression does not recognize any string.

We can now ask our system for variables satisfying:

> prop_repeat:  not (eps p) &&
>               rec s (rep p i j :&: rep p i' j') &&
>               not (rec (rep p (max i i') (min j j')) s)

whereupon we get the following counterexample in about 30 seconds:

% p:  (R(R(R__(T))(R__(T))(T))(R__(T))(T))
% i:  (Nat(Nat(Nat_)))
% i': (Nat(Nat(Nat_)))
% j:  (Nat(Nat(Nat_)))
% j': (Nat(Nat(Nat_)))
% s:  (List(T)(List(T)(List(T)_)))

\begin{verbatim}
Counterexample!
p:  (Atom A :>: Atom A) :+: Atom A
i:  S (S Z)
i': S Z
j:  S (S Z)
j': S Z
s:  [A,A]
\end{verbatim}

This is a counterexample since 
|rep p (max i i') (min j j')| = |rep p 2 1|, which recognizes
no string, but |rep p [A,A]| does hold.

We list our and LazySmallCheck's run times on
|prop_repeat| above and on two seemingly simpler 
properties, namely: 

|prop_conj: not (eps p) && rec (p :&: (p :>: p)) s|

|prop_iter: i /= j && not (eps p) && rec (iter i p :&: iter j p) s|

The last property uses a function |iter :: Nat -> RE -> RE| which
repeats a regexp a given number of times. The results are found
in Table \ref{regexptable}.

\begin{table}[htd]
\begin{center}

\textit{
\begin{tabular}{l r r }
\em Conjecture & \em Our tool & \em LazySC \\
\hline
|prop_conj|   & 27.2s &  0.6s \\
|prop_iter|   &  6.6s & 17.4s \\
|prop_repeat| & 35.7s & 103s  \\
\end{tabular}
}
\end{center}
\caption{Run times of finding conterexamples
to regular expression conjectures. The properties
are defined in Section \ref{regexp}.}
\label{regexptable}
\end{table}%

If we look more closely at the implementation of the regular expression library 
we find that the calls are duplicated across the branches.
For instance, the |eps| function looks like this:

\begin{code}
eps Eps          = True
eps (p  :+:  q)  = eps p || eps q
eps (p  :&:  q)  = eps p && eps q
eps (p  :>:  q)  = eps p && eps q
eps (Star _)     = True
eps _            = False
\end{code}

Here, we could collapse all the calls |eps p| as described
in the section above, but it is actually enough to just
memoize them as they are exactly the same. (The same holds for |eps q|).
The recursive call structure of the |step| function follows
the same pattern as for |eps| and memoisation is enough there as well.

% \begin{code}
% step  :: RE Token -> Token -> RE Token
% step  (Atom a)   x  = if a == x then Eps else Nil
% step  (p :+: q)  x  =  step p x :+:  step q x
% step  (p :&: q)  x  =  step p x :&:  step q x
% step  (p :>: q)  x  =  (step p x :>: q) :+: 
%                        if eps p then step q x else Nil
% step  (Star p)   x  =  step p x :>: Star p
% step  _          x  = Nil
% \end{code}
% 
% The previous code uses the predicate |eps :: R a -> Bool|
% which answers if a regular expression recognizes 
% the empty string. We can now define the recognizer |rec|
% for an input word:
% 
% \begin{code}
% rec :: RE Token -> [Token] -> Bool
% rec p []      = eps p
% rec p (x:xs)  = rec (step p x) xs
% \end{code}
% 
% The first example we look at is 
% relating conjunction of regular expressions |(:&:)|
% and sequential composition |(:>:)|:
% 
% > not (eps p) && rec (p :&: (p :>: p)) s 
% 
% On this example, we get a counterexample after 28
% seconds, having explored the right part of the
% expression, but the list a little too far:
% 
% \begin{verbatim}
% p: (R(R(R__(T))_(T))(R__(T))(T))
% s: (List(T)(List(T)(List(T)(List(T)_))))
% 
% Counterexample!
% p: Star (Atom B) :>: Atom B
% s: Cons B (Cons B Nil)
% \end{verbatim}
% 
% The second  property we looked at 
% involves iterates a regular expression
% with |iter| a number of times:
% 
% \begin{code}
% iter :: Nat -> R a -> R a
% iter Z     _ = Eps
% iter (S n) r = r :>: iter n r
% \end{code}
% 
% The property is now is trying to find such an expression
% |p|, a word |s| and two numbers |i| and |j| such that:
% 
% > i /= j && not (eps p) && rec (iter i p :&: iter j p) s
% 
% On this example we explore this: 
% 
% \begin{verbatim}
% i: (Nat(Nat(Nat_)))
% j: (Nat(Nat(Nat_)))
% p: (R(R(R__(T))_(T))(R__(T))(T))
% s: (List(T)(List(T)(List(T)_)))
% 
% Counterexample!
% i: S (S Z)
% j: S Z
% p: Star (Atom A) :>: Atom A
% s: Cons A (Cons A Nil)
% \end{verbatim}
% 
% Given this:
% 
% \begin{code}
% subtract1 :: Nat -> Nat
% subtract1 Z      = Z
% subtract1 (S x)  = x
% 
% rep :: R T -> Nat -> Nat -> R T
% rep p i      (S j)  = (cond (isZero i) :+: p) 
%                     :>: rep p (subtract1 i) j
% rep p Z      Z      = Eps
% rep p (S _)  Z      = Nil 
% \end{code}
% 
% Prove this:
% 
% > not (eps p)  && rec (rep p i j :&: rep p i' j') s 
% >              && not (rec (rep p (i `max` i') (j `min` j')))
% 
% This is what we get:
% 
% \begin{verbatim}
% p8: (R(R(R__(T))(R__(T))(T))(R__(T))(T))
% i0: (Nat(Nat(Nat_)))
% i': (Nat(Nat(Nat_)))
% j0: (Nat(Nat(Nat_)))
% j': (Nat(Nat(Nat_)))
% s: (List(T)(List(T)(List(T)_)))
% 
% == Try solve with 74 waits ==
% Counterexample!
% p8: (Atom A :>: Atom A) :+: Atom A
% i0: S (S Z)
% i': S Z
% j0: S (S Z)
% j': S Z
% s: Cons A (Cons A Nil)
% \end{verbatim}

% \subsection{Ambiguity detection}
% 
% Showing stuff, inverse.
% 
% \subsection{Integration from Differentiation}
% Deriving expressions, inverse.

\subsection{Synthesising turing machines}

Another example we considered was a simulator
of turing machines. The tape symbols are
either empty (|O|), or |A| or |B|:

> data A = O | A | B

The actions are either halting or moving
right or left and entering a new state represented with a |Nat|:

> data Action = Lft Nat | Rgt Nat | Stp

The machine is then a function from the state (a |Nat|), and
a the symbol at the tape head |A|, to a symbol to be written
and a new head:

> type Q' = (Nat,A) -> (A,Action)

but we (currently) don't support functions we represent this 
tabulated in a list instead:

> type Q      = [((Nat,A),(A,Action))]

(This transformation from lists to tables could be
done automatically, with the addition of a default value.)
A configuration of the machine is a state, and a zipper
of the tape head: the reversed list of the symbols to
the left, and the current symbol consed on to the symbols to the right:

> type Configuration  = (Nat,[A],[A])

The |step| function advances the machine one step, which 
either terminates with the final tape, or 
ends up in a  new configuration.

> step :: Q -> Configuration -> Either [A] Configuration

The |steps| function runs |step| repeatedly
until the machine terminates.

> steps  :: Q -> Configuration -> [A]

This function may of course not terminate, so
the translated functions needs to insert a |postpone|,
as described above.

The entire machine can be run from a starting
tape, by stepping it from the starting state |Zero| with |run|:

> run         :: Q -> [A] -> [A]
> run q tape  = steps q (Zero,[],tape)

We used or system to find turing machines given an input-output pair.

One example is to find the insert function, which puts an intial |B|
to the right place in a sorted list with these input-output pairs:

> run q [A]            == [A] && 
> run q [B,A,A,A,A,B]  == [A,A,A,A,B,B]

Asking our system to find such a |q|, we get this result (pretty-printed, with
literals ints instead of Nats) in ten seconds:
 

\begin{code}
[  ((Succ Zero,         A),  (B,  Stp)),
   ((Succ (Succ Zero),  A),  (A,  Rgt (Succ (Succ Zero)))),
   ((Zero,              B),  (A,  Rgt (Succ (Succ Zero)))),
   ((Succ (Succ Zero),  B),  (B,  Lft (Succ Zero))),
   ((Zero,              A),  (A,  Stp)) ]
\end{code}

This machine contains a loop in state two, which is enters
upon reading an inital |B| (which is replaced with an |A|).
It then uses state two to skip by all the |A|s until 
it comes to a |B|, where it backtracks, and replaces
the last |A| it found with a |B|. If the tape starts with
|A| the program terminates immediately.

In the above example we found by experimentation that 
it was necessary to have no less than four A in the example,
otherwise it the returned machine would "cheat" and instead
of creating a loop, just count.

In this example it is crucial to use |postpone| to
be able to handle the possibly non-terminating |steps| function.
In systems like Reach \cite{reach}, it is possile
to limit the expansion of the program on the number of unrollings
of recursive functions. Our method with |postpone| does exactly
this, but there is no need to decide beforehand how many
unrollings are needed, it is all done dynamically.


% ------------------------------------------------------------------------------

% \section{Experimental evaluation}
% 
% And again, there is the merge sort times.
% 
% Regexp was evaluated against leon and
% lazy small check. leon timed out on all of them
% 
% We evaluated the type checker against 
% lazy small check with a timeout of 300s.
% 
% Turing machines were evaluated...
% LSC timed out.

% 
% Compare some examples against Leon.
% 
% Compare some examples against Lazy SmallCheck.
% 
% Compare with/without memoization and with/without merging function calls.
% 
% Compare with/without conflict minimization?
% 
% Show timings of the above examples.

% ------------------------------------------------------------------------------

\section{Related Work}

One big source of inspiration for this work is the Leon system\cite{leon},
Their setup is similar to ours, but encodes the problem into 
uninterpreted functions in a SMT solver. Another difference
is that their focus is mainly on proving properties (stated as contracts)
rather than finding counterexamples. Using uninterpreted
functions in a SMT solver helps in this regard in that it can
see equivalences between values that are "far apart".

QuickCheck\cite{quickcheck} is an embedded DSL for finding 
counterexamples for Haskell by using randomized testing.
A potential drawback of that approach is that you
have to write generators of random values suitable 
for the domain. This becomes especially important in 
the presence of preconditions, where the generator can
essentially become the inverse of the predicate.

One way to avoid the generator problem is to enumerate
input values for testing. This is the approach taken in
for instance SmallCheck \cite{smallcheck} which
enumerates values on depth, and can also handle nested quantifiers.
Another work is Feat \cite{feat},
which develops an algebra for enumerating values based on size.
Using size instead of depth as measure can sometimes be 
beneficial as it grows slower, allowing for greater granularity.

By evaluating tagged undefined values (in a lazy language),
it can be observed which parts of the input is actually
demanded by the program. The forced parts of the value
can be refined with concrete values and then repeated.
This technique is called lazy narrowing. 
When refining the values, it 
might be the case that you start exploring a path which
does not lead to a counterexample. 
One example of this is \cite{reach}, which allows
to do this backtracking either upon reaching a predetermined
depth of the value or of the recursion. LazySmallCheck\cite{lazysc}, 
combined the ideas from SmallCheck and Reach to do lazy narrowing
on the depth of the values as a DSL in Haskell.

Liquid types.

Curry (lazy narrowing?)

EasyCheck

Catch

% ------------------------------------------------------------------------------

\section{Discussion and Future Work}

Parallelize expansion.

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

Still make some manual choices: what to memo, what to label.

Our method does not work well when: (1) Expansion does the wrong thing (in which case you can do this by hand), (2) Expansion is too careful, too many small steps, (3) the SAT-problem becomes too big (all intermediate datastructures are remembered), or (4) the SAT-problem is too hard. 

It is perhaps surprising that this is even possible; coding a search problem over a program containing recursive functions over recursive datastructures in terms of a SAT-problem, which is inherently finite.

% ------------------------------------------------------------------------------

%\appendix
%\section{Appendix Title}

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

