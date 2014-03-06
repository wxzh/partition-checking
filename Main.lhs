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
    \textbf{Types} & \type & ::= & \alpha \mid \type \arrow \type 
    \mid \forall \alpha. \type \\ 
    \textbf{Type Contexts} & \Gamma & ::= & \epsilon \mid \Gamma, \relation{x}{\type} \\
    \textbf{Expressions} & e & ::=  & x \mid c \mid C~\overline{e} \mid e \oplus e \mid \texttt{let}\;x = e\;\texttt{in}\;e \mid \\
                         &&&\lambda x . e \mid e\;e \mid \texttt{case}\;e\;\texttt{of}\;[p_i\arrow e_i]_{i\in I} \\
    \textbf{Patterns} & p & ::= & x \mid \_ \mid C~p \\ 
    \textbf{Values} & v & ::= & c \mid C\; \overline{v} \mid \lambda x . e  \\ 

\ea
\\ \\

\ba{llrl} 
\textbf{Environments} & \rho & ::= & \epsilon \mid \rho[x\mapsto v]  
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

  (\texttt{Val}) & 
\myirule{}{
            \rho,v \Downarrow v
} \\ \\

  (\texttt{Bin}) & 
\myirule{
           \rho,e_1\Downarrow c_1\;\;\;\rho,e_2\Downarrow c_2
 }{
           \rho,e_1\oplus e_2\Downarrow c_1\oplus c_2
} \\ \\

  (\texttt{Let}) & 
\myirule{
           \rho,e_1\Downarrow v_1\;\;\;\rho[x\mapsto v_1],e_2\Downarrow v_2
 }{
           \rho,\texttt{let}\;x = e_1\;\texttt{in}\;e_2\Downarrow v_2
} \\ \\

  (\texttt{App}) & 
\myirule{
           \rho,e_1 \Downarrow \texttt{fun}\; f(x).e\;\;\; \rho, e_2 \Downarrow v_2\\
           \rho[f\mapsto v_1][x\mapsto v_2],e\Downarrow v\;\;\;
 }{
           \rho,e_1\;e_2 \Downarrow v
} \\ \\

  (\texttt{Cas}) & 
\myirule{
           \rho, e \Downarrow v_1 \\
           \rho' = match\; v_1\; p_i\;\;\;
           \rho\rho',e_i\Downarrow v_2
 }{
           \rho,\texttt{case}\;e\;\texttt{of}\;[p_i\arrow e_i]_{i\in I} \Downarrow v_2
} \\ \\

\ea

\eda
}

 
\section{Related Work}\label{sec:related}
%include RelatedWork.lhs

\bibliographystyle{plain}
\bibliography{literature}

\end{document}
