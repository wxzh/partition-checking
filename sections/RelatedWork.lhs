\section{Related Work}
 
We relate our work to ...

 
\subsection{Property-based Testing}

A lot of work have been done to improve \qc in various aspects.

Writing generators for mutually recursive algebraic datatypes is difficult.
Some works have been done for automatically generating generators.
 
\paragraph{Feat}
Feat~\cite{duregaard2013feat} tries to automatically generate uniformly distributed random test cases satisfying a precondition through functional enumeration for algebraic datatypes.
 
\paragraph{Luck}
Luck~\cite{lampropoulosmaking} is a domain-specifc language that aims to significantly reduce the amount of hand-written generator code through light annotations.
 
\paragraph{Smartcheck} Smartcheck~\cite{pike2014smartcheck} aims to provide users with more consice counterexamples without struggling writing \emph{shrink} by hand, Based on the counterexample found by \qc, Smartcheck tries to shrinks it by replacing it with generalises a class of counterexamples of by replacing it with its sub-values.
 
\paragraph{SmallCheck}
SmallCheck~\cite{SmallCheck:Runciman:2008} adopts \emph{bounded-exhaustive} testing strategy instead of \emph{random} testing based on the \emph{small scope hypothesis},
which states that most of the bugs can be found by exhausitively testing a small part of the input set.
In some sense, \name is more like \sch than \qc, which exhausitively checks all paths up to some depth.
However, \sch suffers from the problem of combinatorial explosion, i.e., the number of distinct cases may grow exponentially with the depth.
% especially when an algebraic datatype has dozens or hundreds of constructors.
As a result, it will get stuck in a small depth leaving most of interesting test cases untouched.
For example, enumerating a list of integers of 32 bits up to length 2 needs approximate $2^{64}$ cases in total, which is already an intractable number.
In addition, the same depth number means different to different datatypes. Hence, it is hard for the users to specify the depth when testing.
In fact, it is a waste to test inputs that cover the same execution path.
Though \name faces the similar issue since the number of execution paths can be infinite, in practice it is able to cover excution paths that rather complicated inputs can triger.

\subsection{Symbolic Execution}
Symbolic execution was firstly proposed in the 1970s~\cite{king1976symbolic} and has regained a lot of attentions recently with the rapid development of modern constraint solvers, e.g. Z3~\cite{de2008z3} and CVC4~\cite{barrett2011cvc4}.
Several testing tools have been developed which leverage symbolic execution to imperative languages,
e.g., DART~\cite{godefroid2005dart} and CUTE~\cite{sen2005cute} for C and PEX~\cite{Pex:Tillmann:2008} for .NET.
These tools combine dynamic test generation and random testing.
% It is relatively not popular among functional languages. We argue that functional languages are better candidates for performing symbolic execution.
% because (1) no side effect (2) simple core language which makes it easier to reason the program.

\subsection{Contract Verification}
\paragraph{Leon} Leon~\cite{blanc2013overview} is a verification system built upon the pure subset of the Scala programming language.
Users need to annotate the program with pre and post conditions as contract.
Given an input program, Leon will generate verification conditions according to the contract.
Unlike our approach, Leon will try to verify that all feasible execution paths end up with a \texttt{True} for the purpose of proving.
Hence, an endless path would trap Leon and make it time out.
\name, however, can escape from this situation if reaching the maximum depth and continue searching in other paths.

\paragraph{Target}
Seidel at el.~\cite{seidel2014type} proposed a technique called type target testing which treats types as specifications - types of parameters of a function are precondition and the result type is served as the postcondition. When testing a function, types are firstly tranlated to be formula which can be fed to an SMT solver to get a model. Then the model is decoded as the input of this function to obtain a result of the function and the result is checked according to the post-condition. However, users need to define custom type for describing complex preconditions and/or postconditions. Different from our approach, it adopts black-box approach which share the similar issues with \qc.

\paragraph{Relative}
Nguyen and Van Horn~\cite{nguyen2014relatively} apply symbolic execution to functional programming languages for generating counter-examples for higher-order functions.
They use first order constraints to reconstruct higher-order inputs.
But the core language they use lacks support for algebraic datatypes and pattern matching which is a core feature of modern functional langugaes.
