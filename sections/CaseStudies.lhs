\section{Case Studies}
 
 In this section we will show the effectiveness for finding subtle bugs and efficiency of \name. We developed a prototype in Haskell based on the semantics we described on Section~\ref{sec:formal}.
 
\name let us write machine-checkable declarative specification through conditional properties.
 
 
We compare \name with \qc and Leon. Leon~\cite{blanc2013overview} is a verification tool built upon purely functional subset of the Scala programming language. Property-based testing can be simulated through defining boolean functions annotated with \texttt{holds} construct.
 
Unfortunately, there is no common benchmarks for comparing property-based testing approaches. We adopt some of the benchmarks from the Leon website~\footnote{\url{https://leon.epfl.ch/}} with a couple of slightly more complicated programs we design.

 The benchmarks were run on a computer equipped with two CPUs at 8.0 GB of RAM. We used Z3 version 4.3.2.
 
Table.~\ref{table:time} compares the time for finding the first counterexample for each approach. The result shows that from the performance perspective, our approach is competative to \qc and faster than Leon. In terms of finding bugs, both \name and Leon can find corner case bugs which \qc can not. For complicated programs like TypeSound, Leon times out.
 
% in practice some program structures require too many unrollings and Leon is likely to timeout (or being out of memory) before finding the counterexample
 
 
%We set the time out to be ? minutes.
 
\paragraph{Reverse}
 
\paragraph{Inserting into a Red-Black Tree}
 
\paragraph{Searched}
 
\paragraph{Summary of Results}
 
\begin{table}
 \center
\begin{tabular}{lrrrr}
  Program          & FCore & QuickCheck & Leon \\
  \hline
  Reverse & 3.52   & 3.31    & 35.6 \\
%  ListOperations   & NA    & NA    & 25 \\
  SearchLinkedList & 8.7   & 7.5    & 24.2 \\
  RedBlackTree     & 3.8   & NA    & 100.7 \\
%  AvlTree          & NA    & NA    & NA \\
  HeapSort         & 30.3  & 1.5   & 151.6 \\
  TypeSound        & 3062.8  & NA    & Timeout \\
  FirstOrderLogic  & 46.5 & NA    & 75.3
  \end{tabular}
  \caption{Comparison of the time to find the first counterexample}\label{table:time}
\end{table}

QuickCheck: generate-and-filter
 
From the table we can see that both \name and Leon can find counterexamples in the first few programs. However, \qc and \qc* can not easily find one.
 
 Comparison of the complexity of the counterexample found

Figure~\ref{table:time} shows the

From Fig.~\ref{table:time} we could see that \name outperforms Leon in general. Moreover, \name can find bugs in ... which Leon can not.

"declarative" specification.

\begin{table}
  \center
\begin{tabular}{lr}
  Program & LOC\\
  \hline
  Reverse           & 0 \\
%  ListOperations    & 0 \\
%  InsertionSort     & 0 \\
  SearchLinkedList  & 0 \\
  HeapSort          & 47 \\
  RedBlackTree      & 21 \\
%  AvlTree           & 8 \\
  TypeSound         & 10 \\
  FirstOrderLogic   & 24 \\
  \end{tabular}
  \caption{Line of code for generators}\label{table:time}
\end{table}

% Limitations?

\subsection{Comparison with \sch}
