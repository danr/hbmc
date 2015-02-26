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

Finding {\em counter examples}, {\em examples}, {\em inverting functions}, for prototype programming, primarily. Secondarily, for showing their absence.

Bounded Model Checking for C. Difference: recursive data structures. Doing this by modelling pointers and the heap does not work.

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

\item We show how a program containing recursive functions over symbolic datatypes can be symbolically executed, generating a SAT-problem.

symbolic simulation of functional programs using a SAT-solver (first)

* incremental implementation (thunks and conflict clause)

* dealing with recursive functions, program transformation

Show how the solver and the generated program can make the search for a countexample more efficient

\cite{apa}

% ------------------------------------------------------------------------------

\section{Main Idea}

Forte, where the user can create (BDD) variables, returning a bool. How about if-then-else on that bool?

Need symbolic booleans that influence all datastructures.

Example: lists.

data List a = Nil | Cons a (List a)

symbolic version:

data List a = List Bit (Maybe (a, List a))

Show case expressions on these lists

case xs of
  Nil -> a
  Cons y ys -> f (y,ys)

becomes:

  let List c myys = xs in
    if c then a else f (fromJust myys)

in constraint style:

...

Language

First-order.
%\begin{
%e ::= x
%     \|  f x1 .. xn
%     \|  K x1 .. xn
%     \|  let x = e1 in e2
%     |  case x of { … ; K y1 .. yk -> e ; … }

Translation into constraints. Define what constraints are. Monadic constraint language. Show API, talk about meaning.

Show translation of datatypes, and generation of case functions. Projection functions.

Current idea is to only use “sinks” in case-expressions. Case expressions are translated into:

  y <- new
  ...
  (constr x =? Ki) ==>
     do yi <- [[ei]]
          yi >>> y
  …
  return y

Show examples.

% ------------------------------------------------------------------------------

\section{Generating Constraints}

\subsection{The Constraint monad}

The constraint monad.

\begin{code}
type C a
instance Monad C

newVar  :: C Prop
insist  :: Prop -> C ()
when    :: Prop -> C () -> C ()
\end{code}

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

Show the API.

\subsection{Representing datatypes}

Show the Val type (Fin?).

\begin{code}
newtype Fin a = Fin [(Prop,a)]

newFin  :: Ord a => [a] -> C (Fin a)
is      :: Ord a => Fin a -> a -> Prop
one     :: a -> Fin a
\end{code}

Show how lists and trees are represented.

\begin{code}
data List a  = List (Fin ListC) (Maybe a) (Maybe (List a))
data ListC   = Nil | Cons

nil        :: List a
nil        = List (one Nil) Nothing Nothing

cons       :: a -> List a -> List a
cons x xs  = List (one Cons) (Just x) (Just xs)

isNil, isCons :: List a -> Prop
isNil   (List c _ _)  = c `is` Nil
isCons  (List c _ _)  = c `is` Cons

selList1 :: List a -> Maybe a
selList1 (List _ mx _) = mx

selList2 :: List a -> Maybe (List a)
selList2 (List _ _ mxs) = mxs
\end{code}

Show how general datatypes are be represented.

equalHere, overloaded.

new, overloaded, with depth.

\subsection{Translating a program into constraints}

Show the syntax of expressions. Assumption: it all terminates.

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

Sorting stuff.

Showing stuff, inverse.

Regular expressions.

Deriving expressions, inverse.

Turing machines?

% --- %

Also show examples of (depth-bound and/or size-bound and/or other-bound) things that terminate without example.

Also show higher-order functions?

% ------------------------------------------------------------------------------

\section{Experimental evaluations}

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

Higher-order functions.

Laziness.

Crashing programs (and respecting laziness).

Targets a la Reach.

Using SMT. Integers (trivial, but how to do recursion over integers that terminates? add check everywhere?). Equality and functions can be used to encode constructor functions, selector functions, function application. This is what Leon does. Gain?

% ------------------------------------------------------------------------------

\section{Conclusions}

This is a hard problem.

We have found a niche, works well (and better than others) for cases where the SAT problem is not too big, and one gains something from combinatorial search power.

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

