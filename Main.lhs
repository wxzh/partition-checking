\documentclass{sigplanconf}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

\usepackage{amsmath}
\usepackage[retainorgcmds]{IEEEtrantools}
\usepackage{color}
\usepackage{multirow}

\usepackage{stmaryrd}
\usepackage{graphicx}
\usepackage{amssymb}
\usepackage{fancyvrb}
\usepackage{url}
\usepackage{pstricks,pst-node,pst-tree}
\usepackage[all]{xy}
\usepackage{framed}

\input{macro-comments}
\input{macros}

\title{Partition Checking}

\authorinfo
{DRAFT}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{document}

\maketitle

\begin{abstract}
Some abstract ...
\end{abstract}

\section{Introduction - Some notes}

Property-based testing (PBT) has established itself as an important
tool for testing functional programs.  The existing approaches to PBT
use for the most part random testing.

In imperative programming random testing has also been widely
used. However, several authors have argued against the drawbacks 
of random testing, while promoting other approaches, such as Symbolic Execution. 
Symbolic execution is interesting for testing because a program path can 
be followed, not only for a concrete input, but for all inputs that satisfy 
the path condition. In random testing, due to the use of a concrete input, 

Symbolic execution seems a very good fit for functional programming. 

Property-based testing is by now a well-established mechanism for testing FP programs;
Property-based testing is usually done using random testing;
In Imperative programming, several researchers have pointed flaws to random testing;
Alternatives include among others, Symbolic Evaluation
Benefits of SE: can follow a path symbolically, without concrete values
SE seems a perfect fit for FP:
  * FP has no side-effects, which are difficult to deal with in SE
  * FP often defines programs by pattern matching, when the input size for each path tends to be quite big
paths with large input sizes benefit from SE
* SE combined with property-based testing can improve significantly the coverage, for programs that have such large paths

so the additional thing in FP is higher-order values
which is what the Racket guys have been emphasizing and exploring as well
that should set us apart from Imperative Programming
right
and, hopefully, Property-based Testing + FP with datatypes
should set us apart from the Racket guys

so, in SE the branching constructs are obviously the most intersting aspects
but there is a big gap in expressiveness between a simple "if"
and case analysis
case analysis introduces binding, for example

Large Paths + Parametric definitions + White Box Testing 


> {-# LANGUAGE FlexibleInstances #-}
> import Test.QuickCheck
> import Data.List

\section{Correctness}
\include{correctness} \label{sec:correctness}

reverse

> reverse1 :: [a] -> [a]
> reverse1 [] = []
> reverse1 (x:xs) = reverse1 xs ++ [x]
>
> reverse2 :: [a] -> [a]
> reverse2 xs = revAcc xs []
>   where revAcc [] acc = acc
>         revAcc (x:xs) acc = revAcc xs (x:acc) 
>
> reverse3 :: [a] -> [a]
> reverse3 = foldr snoc []
>   where snoc x xs = xs ++ [x] 
>
> prop_rev_reg :: [Int] -> Bool
> prop_rev_reg xs = reverse1 xs == reverse2 xs && reverse2 xs == reverse3 xs
> 
> prop_rev_twice :: [Int] -> Bool
> prop_rev_twice xs = reverse1 (reverse1 xs) == xs
>
> prop_rev_length :: [Int] -> Bool
> prop_rev_length xs = length (reverse1 xs) == length xs
>
> prop_rev_elem :: ([Int],Int) -> Property
> prop_rev_elem (xs,i) = i < length xs && i >=0 ==> elem (xs!!i) (reverse xs)

filter

> filterPos :: [Int] -> [Int]
> filterPos [] = []
> filterPos (x:xs) = if x>0 then x:filterPos xs else filterPos xs
>
> prop_filterP :: [Int] -> Bool
> prop_filterP xs = all (>0) (filterPos xs) 
>
> prop_filterP_length :: [Int] -> Bool
> prop_filterP_length xs = length xs >= length (filterPos xs)
>
> prop_filterP_twice :: [Int] -> Bool
> prop_filterP_twice xs = filterPos (filterPos xs) == xs

map

> prop_rev_map :: ([Int],Int -> Int) -> Bool
> prop_rev_map (xs,f) = reverse (map f xs) == map f (reverse xs)
>
> instance Show (Int->Int) where

sort

> prop_sort :: (Int,Int,[Int]) -> Property
> prop_sort (i,j,xs) = i<=j && j < length xs && i >=0 ==> sort xs !! i <= sort xs !! j
>
> prop_sort1 :: [Int] -> Bool
> prop_sort1 xs = isSorted (sort xs)

\subsection{Equational Reasoning}
<       prop_rev_reg

<       xs = []
<
<       reverse1 xs == reverse2 xs
<   ==  {- definitions of |reverse1| and |reverse2|-}
<       [] == revAcc xs []
<   ==  {- definition of |revAcc| -}
<       [] == []
<   ==  
<       True

<       xs = [X]
<       reverse1 xs == reverse2 xs
<   ==  
<       reverse1 [] ++ [X] == revAcc [X] []
<   ==  
<       [X] == revAcc [] (X:[])
<   == 
<       True

The polymorphic case is always simple. Add we are exploiting the fact that the function is polymorphic. 
On the contrary, QuickCheck is weak here. It is not easy to tell whether the test performed on a selected
monomorphic type is sufficient or not.   


<       prop_filterP

<       xs = []
<
<       all (>0) (filterPos []) 
<   ==
<       all (>0) []
<   ==
<       True

<       xs = [X]
<
<       all (>0) (filterPos [X]) 
<   ==  {- Both branches are True -}
<       True

<       xs = [X] where X > 0
<
<       all (>0) (filterPos [X])
<   ==  
<       all (>0) (X:filterPos [])
<   == 
<       all (>0) [X]
<   == 
<       True

<       xs = [X] where X <= 0
<
<       all (>0) (filterPos [X])
<   ==  
<       all (>0) (filterPos [])
<   == 
<       all (>0) []
<   == 
<       True

<       xs = [X,Y]
<
<       all (>0) (filterPos [X,Y]) 
<   ==  {- All branches are True -}
<       True

<       xs = [X,Y] where X > 0
<
<       all (>0) (filterPos [X,Y])
<   ==  
<       all (>0) (X:filterPos [Y])
<   ==  {- All branches are True -}
<       True

<       xs = [X,Y] where X > 0, Y > 0
<
<       all (>0) (filterPos [X,Y])
<   ==  
<       all (>0) (X:filterPos [Y])
<   ==
<       all (>0) (X:Y:filterPos [])
<   ==  
<       all (>0) [X,Y]
<   ==  
<       True

<       xs = [X,Y] where X > 0, Y <= 0
<
<       all (>0) (filterPos [X,Y])
<   ==  
<       all (>0) (X:filterPos [Y])
<   ==
<       all (>0) (X:Y:filterPos [])
<   ==  
<       all (>0) [X]
<   ==  
<       True

<       xs = [X,Y] where X <= 0
<
<       all (>0) (filterPos [X,Y])
<   ==  
<       all (>0) (filterPos [Y])
<   ==  {- All branches are True -}
<       True

<       xs = [X,Y] where X <= 0, Y > 0
<
<       all (>0) (filterPos [X,Y])
<   ==  
<       all (>0) (filterPos [Y])
<   ==
<       all (>0) (Y:filterPos [])
<   ==  
<       all (>0) [Y]
<   ==  
<       True

<       xs = [X,Y] where X <= 0, Y <= 0
<
<       all (>0) (filterPos [X,Y])
<   ==  
<       all (>0) (filterPos [Y])
<   ==
<       all (>0) (filterPos [])
<   ==  
<       all (>0) []
<   ==  
<       True


\section{Formalization}

Template for some rules:

\figtwocol{f:syntax}{Abstract Syntax}{
\small
\bda{l}

\ba{llrl}
%%    \textbf{Types} & \type & ::= & \alpha \mid \type \arrow \type 
%%    \mid \forall \alpha. \type \\ 
%%    \textbf{Type Contexts} & \Gamma & ::= & \epsilon \mid \Gamma, \relation{x}{\type} \\
    \textbf{Expressions} & e & ::=  & x \mid c \mid C~\overline{e}\mid o~\overline{e} \mid 
                         \lambda x . e \mid e_1\;e_2 \mid\\ 
                         &&&\texttt{let}\;f = \lambda x. e_1\;\texttt{in}\;e_2 \mid \texttt{case}\;e\;\texttt{of}\;[C_i~\overline{x}\arrow e_i]_{i\in I} \\
%    \textbf{Patterns} & p & ::= & x \mid C~\overline{x} \\ 
    \textbf{Values} & v & ::= & c \mid C~\overline{v} \mid \langle\lambda x . e,\rho\rangle\\
    \textbf{Symbolic Values} & s & ::= & a \mid c \mid \langle\lambda x . e,\sigma\rangle \mid C~\overline{s} \mid o~\overline{s} \mid a\;s  \\ 
    \textbf{Execution Trees} & t & ::= & s \mid \texttt{case}\;s\;\texttt{of}\;[C_i~\overline{a}\arrow t_i]_{i\in I} \\ %\mid \forall a.t\\

\ea
\\ \\

\ba{llrl} 
\textbf{Environments} & \rho & ::= & \epsilon \mid \rho[x\mapsto v] \\
\textbf{Symbolic Environments} & \sigma & ::= & \epsilon \mid \sigma[x\mapsto t]  
\ea 
\\ \\
\eda
}


\figtwocol{f:syntax}{Operational Semantics}{
\small
\bda{l}

\textbf{Call-by-value Evaluation}
\\ \\

\ba{lc}
\multicolumn{2}{l}{\myruleform{\rho,e\Downarrow v}} \\ \\

  (\texttt{Var}) & 
\myirule{}{
            \rho,x \Downarrow \rho(x)
} \\ \\

  (\texttt{Lit}) & 
\myirule{}{
            \rho,c \Downarrow c
} \\ \\

  (\texttt{Con}) & 
\myirule{          \rho, e_i \Downarrow v_i

}{
            \rho,C~\overline{e} \Downarrow C~\overline{v}} \\ \\

  (\texttt{Prm}) & 
\myirule{
           \rho, e_i \Downarrow v_i
 }{
           \rho,o~\overline{e} \Downarrow o~\overline{v}
} \\ \\

  (\texttt{Lam}) & 
\myirule{
}{
           \rho, \lambda x . e \Downarrow \langle\lambda x . e,\rho\rangle
} \\ \\

  (\texttt{Let}) & 
\myirule{
          \rho, e_1\Downarrow v_1\;\;\; \rho[f\mapsto v_1], e_2 \Downarrow v
 }{
           \rho,\texttt{let}\;f =  e_1\;\texttt{in}\;e_2\Downarrow v
} \\ \\

  (\texttt{App}) & 
\myirule{
           \rho,e_1 \Downarrow \langle\lambda x. e,\rho'\rangle\;\;\; \rho, e_2 \Downarrow v_2\\
           \rho'[x\mapsto v_2],e\Downarrow v\;\;\;
 }{
           \rho,e_1\;e_2 \Downarrow v
} \\ \\

  (\texttt{Cas}) & 
\myirule{
           \rho, e \Downarrow v \;\;\;
           \rho_i = match\; v\; (C_i~\overline{x})\;\;\;
           \rho\rho_i,e_i\Downarrow v_i
 }{
           \rho,\texttt{case}\;e\;\texttt{of}\;[C_i~\overline{x}\arrow e_i]_{i\in I} \Downarrow v_i
} \\ \\

\ea

\eda
}


\figtwocol{f:syntax}{Symbolic Operational Semantics}{
\small
\bda{l}

\textbf{Symbolic Evaluation}

\\ \\

\ba{lc}
\multicolumn{2}{l}{\myruleform{\sigma,e\Downarrow t}} \\ \\

  (\texttt{Var}) & 
\myirule{}{
            \sigma,x \Downarrow \sigma(x)
} \\ \\

  (\texttt{Lit}) & 
\myirule{}{
            \sigma,c \Downarrow c
} \\ \\

%  (\texttt{Con}) & 
%\myirule{          \sigma, e_i \Downarrow t_i \;\;\;
%                   C~\overline{t}\Downarrow t

%}{
%            \sigma,C~\overline{e} \Downarrow t} \\ \\

  (\texttt{Prm}) & 
\myirule{          \sigma, e_i \Downarrow t_i \;\;\;
                   (C\!/\!o,\overline{t})\Downarrow_o t

}{
            \sigma,C\!/\!o~\overline{e} \Downarrow t} \\ \\

  (\texttt{Lam}) & 
\myirule{
          
}{
           \sigma, \lambda x . e \Downarrow \langle\lambda x.e,\sigma\rangle
} \\ \\

  (\texttt{Let}) & 
\myirule{
           \sigma, e_1 \Downarrow t_1 \;\;\;
           \sigma [f\mapsto t_1], e_2 \Downarrow t
 }{
           \sigma,\texttt{let}\;f = e_1\;\texttt{in}\;e_2\Downarrow t
} \\ \\


%  (\texttt{Con}) & 
%\myirule{
%}{
%            \sigma,C_n \Downarrow \lambda \alpha_1 \ldots \lambda \alpha_n .~C_n~\overline{\alpha}
%} \\ \\

  (\texttt{App}) & 
\myirule{
           \sigma, e_1 \Downarrow t_1\;\;\; \rho, e_2 \Downarrow t_2\\
           (t_1,t_2) \Downarrow_a t
 }{
           \sigma,e_1\;e_2 \Downarrow t
} \\ \\



  (\texttt{Cas}) & 
\myirule{
           \sigma, e \Downarrow t_1 \\
         %%  \rho_i = match\; v\; p_i\;\;\;
           \sigma[\overline{x} \mapsto \overline{a}],e_i\Downarrow t_i \\
           (t_1,[C_i~\overline{a} \arrow t_i]_{i\in I}) \Downarrow_c t
 }{
           \sigma,\texttt{case}\;e\;\texttt{of}\;[C_i~\overline{x}\arrow e_i]_{i\in I} \Downarrow t
} \\ \\


\ea

\eda
}


\figtwocol{f:syntax}{Auxiliary Definitions}{
\small
\bda{l}

\\ \\

\ba{lc}

\multicolumn{2}{l}{\myruleform{(C\!/\!o,\overline{t})\Downarrow_o t}} \\ \\

  (\texttt{Val}) & 
\myirule{}{
            (C\!/\!o,\overline{s}) \Downarrow_o C\!/\!o~\overline{s}
} \\ \\

  (\texttt{Case}) & 
\myirule{ (C\!/\!o,\overline{s}~t_i~\overline{t})\Downarrow_o t
%\texttt{case}\;s\;\texttt{of}\;[p_i\arrow C\!/\!o~\overline{s}~t_i~\overline{t}]_{i\in I}\Downarrow t
}{
          (C\!/\!o,\overline{s}~(\texttt{case}\;s\;\texttt{of}\;[p_i\arrow t_i]_{i\in I})~\overline{t}) \Downarrow_o \texttt{case}\;s\;\texttt{of}\;[p_i\arrow t]_{i\in I}
} \\ \\



\multicolumn{2}{l}{\myruleform{(t_1,t_2) \Downarrow_a t}} \\ \\

%%  (\texttt{M-Var}) & 
%%\myirule{
%%}{
%%            \alpha~t_1 \Downarrow \alpha~t_1 
%%} \\ \\

  (\texttt{Var1}) & 
\myirule{
}{
            (a,s) \Downarrow_a a~s
} \\ \\

  (\texttt{Var2}) & 
\myirule{
}{
            (a,\texttt{case}\;s\;\texttt{of}\;[p_i\arrow t_i]_{i\in I}) \Downarrow_a \texttt{case}\;s\;\texttt{of}\;[p_i\arrow a~t_i]_{i\in I}
} \\ \\

  (\texttt{Fun}) & 
\myirule{ \sigma[x\mapsto t_2],e\Downarrow t
}{
           (\langle\lambda x.e,\sigma\rangle,t_2)\Downarrow_a t
} \\ \\


  (\texttt{Case}) & 
\myirule{
            (t_i,t) \Downarrow_a t'_i
}{
            (\texttt{case}\;s\;\texttt{of}\;[p_i\arrow t_i]_{i\in I},t) \Downarrow_a \texttt{case}\;s\;\texttt{of}\;[p_i\arrow t'_i]_{i\in I}
} \\ \\




%%\multicolumn{2}{l}{\myruleform{s~t_1 \Downarrow t_2}} \\ \\

%%  (\texttt{M-Var}) & 
%%\myirule{}{
%%            s~\alpha \Downarrow s~\alpha 
%%} \\ \\

%%  (\texttt{M-Symbol}) & 
%%\myirule{}{
%%            s_1~s_2 \Downarrow s_1~s_2 
%%} \\ \\

%%  (\texttt{M-Fun}) & 
%%\myirule{
%%           
%%}{
%%             s~(\lambda \alpha . t) \Downarrow s~(\lambda \alpha . t)
%%} \\ \\



\multicolumn{2}{l}{\myruleform{(t_1,[C_i~\overline{a} \arrow t_i]_{i\in I}) \Downarrow_c t}} \\ \\

  (\texttt{Nest}) & 
\myirule{(t_i,alts)\Downarrow_c t_i'
}{
            (\texttt{case}\;s_1\;\texttt{of}\;[C_i~\overline{a} \arrow t_i]_{i\in I},alts) \Downarrow_c \\ \texttt{case}\;s_1\;\texttt{of}\;[C_i~\overline{a}\arrow t_i']_{i\in I}
} \\ \\

  (\texttt{Other}) & 
\myirule{
}{
            (s,[C_i~\overline{a}\arrow t_i]_{i\in I}) \Downarrow_c \texttt{case}\;s\;\texttt{of}\;[C_i~\overline{a} \arrow t_i]_{i\in I}
} \\ \\

%%  (\texttt{M-Match}) & 
%%\myirule{
%%}{
%%            C_i~\_, [C_i~\_ \arrow t_i]_{i\in I} \Downarrow t_i
%%} \\ \\


\ea

\eda
}




 
\section{Related Work}\label{sec:related}
%include RelatedWork.lhs

\bibliographystyle{plain}
\bibliography{literature}

\end{document}
