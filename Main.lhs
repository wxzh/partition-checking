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


reverse

> reverse1 :: [a] -> [a]
> reverse1 [] = []
> reverse1 (x:xs) = reverse xs ++ [x]
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

<       evalWriter (logfib (n + 2))
<   ==  {- unfold |logfib| and |fix| -}
<       evalWriter (log . fib2 . logfib ( n + 2))
<   ==  {- unfold |log| -}
<       evalWriter ( do  tell "entering fib." 
<                        fib2 logfib (n + 2))
<   ==  {- unfold |fib2| \& reduce case -}    
<       evalWriter ( do  tell "entering fib"
<                        f1 <- logfib (n + 1)
<                        f2 <- logfib n
<                        return (f1 + f2))
<   ==  {- unfold |return| -}
<       evalWriter ( do  tell "entering fib"
<                        f1 <- logfib (n + 1)
<                        f2 <- logfib n
<                        Writer (f1 + f2,""))
<   ==  {- unfold |>>=| -}
<       evalWriter ( do  tell "entering fib"
<                        f1 <- logfib (n + 1)
<                        Writer  (evalWriter (Writer (f1 + evalWriter (logfib n),""))
<                                ,execWriter (logfib n) ++ 
<                                 execWriter (Writer (f1 + evalWriter (logfib n),""))))
<   ==  {- (1) |evalWriter (Writer (x,y)) == x| and (2) |execWriter (Writer (x,y)) == y| -}
<       evalWriter ( do  tell "entering fib"
<                        f1 <- logfib (n + 1)
<                        Writer  (f1 + evalWriter (logfib n)
<                                ,execWriter (logfib n) ++ ""))
<   ==  {- (3) |l ++ "" == l| -}
<       evalWriter ( do  tell "entering fib"
<                        f1 <- logfib (n + 1)
<                        Writer  (f1 + evalWriter (logfib n)
<                                ,execWriter (logfib n)))
<   ==  {- unfold |>>=| -}
<       evalWriter ( do  tell "entering fib"
<                        Writer  (evalWriter (Writer  (evalWriter (logfib (n + 1)) + evalWriter (logfib n)
<                                                     ,execWriter (logfib n)))
<                                ,  execWriter (logfib (n+1)) ++
<                                   execWriter (Writer  (evalWriter (logfib (n + 1)) + evalWriter (logfib n)
<                                                       ,execWriter (logfib n)))))
<   ==  {- |evalWriter (Writer (x,y)) == x| and |execWriter (Writer (x,y)) == y| -}
<       evalWriter ( do  tell "entering fib"
<                        Writer  (evalWriter (logfib (n+1))  +   evalWriter (logfib n)
<                                ,execWriter (logfib (n+1))  ++  execWriter (logfib n)))
<   ==  {- unfold |>>=| -}
<       evalWriter ( Writer  (evalWriter (Writer  (evalWriter (logfib (n+1))  +   evalWriter (logfib n)
<                                                 ,execWriter (logfib (n+1))  ++  execWriter (logfib n)))
<                            ,  execWriter (tell "entering fib.") ++
<                               execWriter (Writer  (evalWriter (logfib (n+1))  +   evalWriter (logfib n)
<                                                   ,execWriter (logfib (n+1))  ++  execWriter (logfib n)))))
<   ==  {- |evalWriter (Writer (x,y)) == x| -}
<       evalWriter (logfib (n + 1)) + evalWriter (logfib n)
<   ==  {- |induction hypotheses| -}
<       runId (slowfib2 (n + 1)) + runId (slowfib2 n)
<   ==  {- (4) |runId (slowfib2 (n+1)) + runId (slowfib2 n) == runId (slowfib2 (n+2)| -}
<       runId (slowfib2 (n+2))

\end{document}