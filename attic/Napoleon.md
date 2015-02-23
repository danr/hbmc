% \Large Symbolic Evaluation of Functional Programs
% Dan Rosén, Koen Claessen
% Dec 12, 2014

#

\begin{center}
{\LARGE

      sort xs = sort ys
    $\Rightarrow$ xs = ys

\pause

$\exists$ xs ys . sort xs = sort ys
    $\wedge$ xs $\neq$ ys \pause $\wedge$ length xs $\geq$ 10

}
\end{center}

# \huge SAT=

\begin{center}
{\Huge

\begin{tabular}{c c l}

$\phi \vee \psi$   & \quad $\phi \Leftrightarrow \psi$ & \quad $\neg \phi$ \\

$\phi \wedge \psi$ & \quad $\phi \Rightarrow \psi$     & \quad x, y, z, $\ldots$

\end{tabular}

\begin{tabular}{ccc}
\pause x $\wedge$ $\neg$x &  \pause \verb~UNSAT~      & \\

\pause x $\vee$   $\neg$x &  \pause \verb~SAT~\pause, &   \verb~x=True~
\end{tabular}

}
\end{center}

# \huge SMT=

\begin{center}
{\LARGE
    SAT: $\vee$, $\wedge$,
        $\Leftrightarrow$,
        $\Rightarrow$, x, y, z, $\ldots$

\pause

  and uninterpreted functions:

    f(x,y), g(h(x),z), =, $\neq$

\pause

  and linear integer arithmetic:

    a + b, c - d, <, $\leq$, i, j, k, ..., =, $\neq$

\pause

  but no quantifiers (today):

      \color{red} $\not\forall$, $\not\exists$
}
\end{center}

#

\Large

    length xs = case xs of
        []   -> 0
        y:ys -> 1 + length ys

\begin{center}

\pause

               (b $\Leftrightarrow$ xs = nil)
$\wedge$ ($\neg$b $\Leftrightarrow$ xs = cons(y,ys))

\pause

$\wedge$       (b $\Rightarrow$ len(xs) = 0)
$\wedge$ ($\neg$b $\Rightarrow$ len(xs) = 1+len(ys))

\pause

$\neg$b $\Rightarrow$ \Big((c $\Leftrightarrow$ ys = nil)
$\wedge$ ($\neg$c $\Leftrightarrow$ ys = cons(z,zs))

$\wedge$ (c $\Rightarrow$ len(ys) = 0)
$\wedge$ ($\neg$c $\Rightarrow$ len(ys)=1+len(zs))\Big)

\pause

$\neg$b $\wedge$ $\neg$c $\wedge$ $\cdots$ $\Rightarrow$ $\bot$

\end{center}

# merging merge

\large

    merge [] ys = ys
    merge xs [] = xs
    merge (x:xs) (y:ys)
        | x < y     = x : merge    xs  (y:ys)
        | otherwise = y : merge (x:xs)    ys

\pause

\large

    merge [] ys = ys
    merge xs [] = xs
    merge (x:xs) (y:ys) = a : merge bs cs
      where
        (a, bs, cs)
            | x < y     = (x,   xs, y:ys)
            | otherwise = (y, x:xs,   ys)

# \LARGE size

\large

* unrollings

* depth

* $\!$ \pause lazy expansion

    \quad

    case $\phi$ $\wedge$ $\neg$b $\wedge$ $\neg$c $\wedge$ $\cdots$ of

    \qquad \verb~SAT~ $\rightarrow$ _counterexample_

    \qquad \verb~UNSAT~ $\rightarrow$ case $\phi$ of

    \qquad \qquad \verb~SAT~ $\rightarrow$ _unroll program based on model_

    \qquad \qquad \verb~UNSAT~ $\rightarrow$ _theorem!_

    \pause

    \quad

    \emph{Satisfiability Modulo Recursive Programs} (Leon),

    Philippe Suter, Ali Sinan Koksal, and Viktor Kuncak

    Static Analysis Symposium (SAS) 2011


# \LARGE contracts

\large

    xs ++ ys = ...
        ensures {res => len res = len(xs) + len(ys)}

\pause

or as a type:

    (++) :: (xs :: [a]) -> (ys :: [a]) ->
            (res :: [a] | len res = len xs + len ys)

\pause

\emph{Liquid Types} (Liquid Haskell),

Ranjit Jhala, Niki Vazou, Eric Seidel

# \LARGE c.f. HipSpec

\Large

\begin{center}

$\forall$ xs ys zs . xs \verb~++~ (ys \verb~++~ zs) = (xs \verb~++~ ys) \verb~++~ zs

\pause

$\forall$ xs ys . qrev xs ys = rev xs \verb~++~ ys

\pause

induction hypothesis:

$\forall$ ys . qrev as ys = rev as \verb~++~ ys

induction conclusion:

qrev (a:as) bs = rev (a:as) \verb~++~ bs

\end{center}

# \LARGE symbolic evaluation can be used for...

\Large

* complex counterexample generation

* bounded model checking

* contracts checking

* theory exploration

(non-exhaustive list!)
