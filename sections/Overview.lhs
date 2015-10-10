\section{Overview}
In this section, we will give a overview of symbolic execution and how it can be applied to property-based testing.

\subsection{Symbolic Execution}
 

% > prop_if    :: Int -> Bool
% > prop_if x  =  if x == 123 then False else True
 
% \Tree [.True [.{x_0 == 0} False ] [.{x_0 != 0} True ] ]
 
To begin with, let us consider the \texttt{take} function, which is a typical functional program with recursion and pattern matching:
 
> data List = Cons Int List | Nil
>
> take                 ::  Int -> List -> List
> take _  Nil          =  Nil
> take 0  _            =  Nil
> take n  (Cons x xs)  =  Cons x (take (n-1) xs)
 
We desugar the program to use explicit pattern matching and if expression for the purpose of demonstration in Fig.~\ref{fig:tree}.

\begin{figure}[ht]
\centering
\begin{minipage}[b]{.45\linewidth}
\begin{spec}
take n xs =
  case xs of
    Nil -> Nil
    Cons x xs' ->   if x == 0
                    then Nil
                    else Cons x (take (n-1) xs')
\end{spec}
\caption{Desugared \texttt{take}}
\label{fig:take}
\end{minipage}
\quad
\begin{minipage}[b]{.45\linewidth}
\Tree [.True [.{$x_1$ = Nil} Nil ] [.{$x_1$ = Cons $x_2$ $x_3$} [.{$x_0$ = 0} Nil ] [.{$x_0 \neq 0$} [.{$x_3$ = Nil} {Cons $x_2$ Nil} ] [.{$x_3$ = Cons $x_4$ $x_5$} [.{$x_0 - 1 = 0$} {Cons $x_2$ Nil} ] {\ldots} ] ] ] ]
\caption{The execution tree for \texttt{take}}
\label{fig:tree}
\end{minipage}
 
%  \caption{Desugared}
 \end{figure}
 
\paragraph{Execution Tree}
The key idea of symbolic execution is to use \emph{symbolic values} rather than concrete ones as the input of the program.
When symbolic executing \texttt{take}, its parameters, $n$ and $xs$, are not instantiated to be any concrete values.
Instead, they are treated as symbolic variables, which represent all possible values of their respective type.
The result of symbolic execution may diverge since control statement(pattern matching and if expression) over symbolic variables can lead the execution to different paths.
Thus, we use a tree, called \emph{execution tree}, to capture all the potential results. Figure ~\ref{fig:tree} visualises the execution tree for the \texttt{take} function.
 
% When symbolic executing this program, $x$ will not be instantiated to be any concrete integers. Instead, we keep $x$ abstract: a symbolic variable that represents all integers. Branching statements may lead to different execution paths. For this example, the if statement makes the result diverges depending on whether $x$ is $123$ or not. Hence to capture all possible execution results, we use a tree to represent like this:
 
%  In concrete execution, the inputs only covers one particular execution path and returns one result; while in symbolic execution,
 
%  The advantage of symbolic execution is that one execution path will be covered only once, which can improve the test coverage dramatically especially when the path covers a large input set.
 
All the symbolic variables have been renamed as $x$ with an unique index starting from 0. The root is always a \texttt{True}; nodes record the decision made when encountering a control statement; leaves are the results of execution.
Note that the tree shown here is incomplete since symbolic executing a recursive funcion may result in an infinite execution tree.
 
\paragraph{Path Condition} A \emph{path condition}(PC) is a quantifier-free first-order formula over symbolic expressions which uniquely determines an execution path.
A PC is constructed by conjuncting the decisions stored in the nodes via traversing the tree from the root down to the leaf.
For example, there are four complete paths showed in Fig.~\ref{take}:
 
 \begin{enumerate}
\item $x_1$ = Nil $\Rightarrow$ Nil
\item ($x_1$ = Cons $x_2$ $x_3$) $\land$ ($x_0 = 0$) $\Rightarrow$ Nil
\item ($x_1$ = Cons $x_2$ $x_3$) $\land$ ($x_0 \neq 0$) $\land$ ($x_3 = Nil$) $\Rightarrow$ Cons $x_2$ Nil
\item ($x_1$ = Cons $x_2$ $x_3$) $\land$ ($x_0 \neq 0)$ $\land$ ($x_3$ = Cons $x_4$ $x_5$) $\land$ ($x_0 - 1 = 0$) $\Rightarrow$ Cons $x_2$ Nil
\end{enumerate}
 
% pattern matching on an symbolic variable will introduce new symbolic variables.
 
 \subsection{Property-based Testing}
To simulate property-based testing, we regard properties as boolean functions.
Therefore symbolic executing on a property will yield a tree whose leaves are boolean values.
A property \emph{holds} if all possible execution paths are ended with a \emph{true}.
To falsify the property, we perform an analysis on the execution tree to check whether there exists a feasible execution path that leads to a \emph{false}.
 
\paragraph{Pruning} There exist infeasible paths in the execution tree: the assertion itself is not satisfiable or contradicts with previous assertions. The two typical cases are: (1) boolean formulas in if expression can never be \emph{true}, e.g.
 
> prop_If    ::  Int -> Bool
> prop_If x  =   if x > 0 && x < 1
>                then False -- infeasible
>                else True
 
There is no $x_0$ such that $x_0 > 0 \land x_0 < 1$ where $x_0$ is an integer
 
(2) The same symbolic variable is pattern matched multiple times, e.g. % can not be constructed by different constructors, e.g.
 
> prop_Case     ::  List -> Bool
> prop_Case xs  =
>   case xs of
>    Nil  -> case xs of
>             Nil  ->  True
>             _    ->  False -- infeasible
>    _    -> True
 
$x_0$ can not be constructed by different constructors simultaneously, hence $$x_0 = Nil \land x_0 = \text{Cons } x_1 \text{ } x_2$$ can never be true.
 
We should filter out the infeasible paths because analysing infeasible paths is a waste of time and infeasible paths that end with \emph{false} may interfere our analysis.
To tackle this issue, everytime a new decision is added to the PC, we query the SMT solver for checking the satisfiability(\texttt{check-sat}) of the new PC.
If it is not satisfiable, we stop and turn to the next branch.

% From the theory perspective, a property holds if and only if all the paths lead to a True. But in realality, we could not verify all possible paths since the number of paths may be infinite. Hence, some cutoff mechanisms such as restricting the execution time or specifying a depth need to be introduced.

\paragraph{Tree Traversal} We adopt \emph{depth first searching} approach when traversing the execution tree to achieve \emph{incremental solving}, which will boost the analysis of the tree.
The condition stored in the parent node is shared by all its children, e.g. for path 3 and path 4, ($x_1$ = Cons $x_2$ $x_3$) $\land$ ($x_0 \neq 0$) are shared.

\paragraph{Cutoff} Depth first searching approach, however, is a double-edged sword. The execution may get stuck in an endless path if the program is recursive e.g. \texttt{take}.
Hence, we introduce a cutoff mechanism which terminates the execution of a path and turns to the next one when hitting the maximum depth specified.
% The meaning of depth is the number of distinct decisions.

\paragraph{Counterexample generation} If a feasible path ends with a \emph{false}, inputs that satisfy the corresbonding PC are all counterexamples.
To give users a concrete instance, we obtain a model from the SMT solver(via \texttt{get-model}) which is one particular assignment of all the symbolic variables.
After a simple parsing and reconstruction, \name will report a counterexample:

% a counterexample

\paragraph{Minimal Counterexample} The simpler the counterexample is, the easier users debug the program. The counterexample found by using the \emph{smallest} depth is said to be \emph{minimal}.
Our definition of depth is slightly different from \sch 's, which is the number of \emph{distinct decisions}.
For example, the four PC listed have depths 1, 2, 3 and 4 respectively.
The depth is not always be the same as the tree depth due to the existence of duplicated decisions, which will be discussed in the next section.

%Bounded-exhausitive testing guarentees the minimalism of counterexamples.

\subsection{Optimisations}

We observed that PCs contain duplicated decisions especially when symbolically executing a recursive program.

Duplicated decisions has several negative aspects:
1) performance penalty. If the new decision introduced is already part of the PC, feasiblity check is needed and only
2) search depth. The duplicated condition will be counted. We may not find the bug for larger scale programs
3) the minimalism of counterexample

In summary, \name allows users to do property-based testing as what they often do using \qc without the trouble of defining generators and shrinking functions

\subsection{A Comparison With \qc}

\name is language-based approach. \qc library-based approach

\paragraph{Advantages} % \name has several advantages over \qc:

\begin{itemize}
  \item \emph{No generators and shrinking.} Users can use the most intuitive way to write properties without paying the effort of defining generators and shrinking functions.

  \item \emph{Able to find corner bugs.} \name adopts white-box approach while \qc uses black-box approach, which enables it to go deep inside the program and exercise the execution path for boundary cases.

  \item \emph{Higher Test coverage.} Concrete execution has a high chance of generating test data for the same execution path that Symbolic execution covers an execution path once and only once.
\end{itemize}

\paragraph{Disadvantages}

\subsection{The Limitation of \name}

\name relies on the external SMT solver for checking the feasibility of path conditions and generating counterexamples. This dependency brings several limitations which we summarise as follows:

\begin{itemize}
 \item \emph{Performance penalty} \qc is much more light-weight compared to \name since comunicating with an SMT solver will bring some performance penalty.
 \item \emph{More restriction on the programs} Not all programs can be symbolically executed. Programs containing conditions that can not be translated to SMT solver recognizable format.
 \item \emph{Scalability}
Large scale programs where a PC may contain hundreds of decisions. To check the satisfiability of such PC may take a long time or even not terminate.
\end{itemize}


\subsection{Testing Higher-order functions}

Currently, we do not support properties that take higher-order functions. The reason is that the SMT solver supports first order functions only.

Nonetheless, we can still write first-order properties to test higher-order functions. For instance, we can validate the map fusion law through the property below:

> prop_MapFusion :: (Bool -> Int) -> (Int -> Bool) -> [Int] -> Bool
> prop_MapFusion f g xs = map f (map g xs) == map (f . g) xs

Recall the property we wrote.

> prop_function :: Fun Int Bool -> Bool
> prop_function f = not ((apply f) 0 == 123)
