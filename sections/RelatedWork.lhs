\section{Related Work}
 
We relate our work to ...

 
\subsection{Property-based Testing}
 
Writing generators for mutually recursive algebraic datatypes is difficult.
Some works have been done for automatically generating generators.
 
\paragraph{SmallCheck}
SmallCheck~\cite{SmallCheck:Runciman:2008} adopts \emph{bounded-exhaustive} testing strategy instead of \emph{random} testing based on the \emph{small scope hypothesis},
which states that most of the bugs can be found by exhausitively testing a small part of the input set.
In some sense, \name is more like \sch than \qc, which exhausitively checks all paths up to some depth.
However, \sch suffers from the problem of combinatorial explosion, i.e., the number of distinct cases may grow exponentially with the depth especially when an algebraic datatype has dozens or hundreds of constructors.
As a result, it will get stuck in a small depth leaving most of interesting test cases untouched.
\name, however, avoids it is not necessary to examine But different from \sch, \name which allows \name to examine
 
 \name guarentees that one execution path will be covered only once,
 
\paragraph{Target}

Target uses refinement type as pre and post conditions
 
\paragraph{Feat}
Feat~\cite{duregaard2013feat}
Automatically generate test cases through functional enumeration.
 
\paragraph{Luck}
 Luck~\cite{lampropoulosmaking} is a domain-specifc language which automatically generates generators
 
\subsection{Symbolic Execution}
Symbolic execution was firstly proposed in the 1970s~\cite{king1976symbolic} and has regained a lot of attentions recently with the rapid development of modern constraint solvers, e.g. Z3~\cite{de2008z3} and CVC4~\cite{barrett2011cvc4}.
Several testing tools have been developed which leverage symbolic execution to imperative languages,
e.g., DART~\cite{godefroid2005dart} and CUTE~\cite{sen2005cute} for C and PEX~\cite{Pex:Tillmann:2008} for .NET.
These tools combine dynamic test generation and random testing.
It is relatively not popular among functional languages. We argue that functional languages are better candidates for performing symbolic execution.
% because (1) no side effect (2) simple core language which makes it easier to reason the program.

 
\subsection{Model-based Testing}
 
\subsection{Contract Verification}
\paragraph{Leon} Leon~\cite{blanc2013overview} is a system for verifying built upon th e pure subset of the Scala programming language. Users
Given an input program, Leon will generate verification conditions according to the contract. Users need to annotate the program with pre and post conditions as contract.
Unlike our approach, Leon will try to verify that all possible execution paths end up with a \texttt{True}. Since the path can be endless, it is likely to timeout before finding a counterexample, while \name can find a counterexample thanks to the cutoff mechanism.
 
\subsection{Constraint-solving}
