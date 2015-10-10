%format (seval (x)) = "\mathcal{S} \llbracket " x "\rrbracket "
%%format (merge op e1 e2) = "\mathcal{M} \llbracket " op "\" e1 " " e2 "\rrbracket "
%format mergeList  = "\overline{\mathcal{M}} "
%format (Lam n t f) = "\lambda (x:\tau).e"
%format (BLam a f) = "\Lambda \alpha.e"
%format (Let x e1 e2) = "\texttt{let } x=" e1 " \texttt{ in } " e2
%format (App e1 e2) = "e_1\;e_2"
%format (TApp e1 e2) = "e\;\tau"
%format ExecutionTree = t
%format vs = "\overline{v}"
%%format Case = "\textbf{case}"
%format (ConstrAlt xs e) = "C~\overline{x} \rightarrow e"
 
 
\section{Formalisation}\label{sec:formal}

\begin{figure}
\begin{spec}
data Expr = Lit               constant value
  | Var String                variable
  | Lam String Type Expr      lambda abstraction
  | PrimOp Expr Op Expr       binary operation
  | App Expr Expr             application
  | BLam String Expr
  | TApp Expr Type
  | Let String Expr Expr
  | Case Expr [Alt]
  | Constr C [Expr]
 
data Op = ADD
        | MUL
        | SUB
        | DIV
        | LT
        | LE
        | GT
        | GE
        | EQ
        | NEQ
        | OR
        | AND

%data Op = + | - | * | / | == | /= | < | <= | > | >= | || | &&
 
\end{spec}
\caption{Syntax}
\label{syntax}
\end{figure}/
 
\begin{spec}
data v
  = c              constant
  | v v             SApp closure
  | v op v          Sop applications
  | SFun x e t
  | C vs            constructor
 
data ExecutionTree
  = v
  | Fork v []
  | NewSymVar SymType ExecutionTree
 
\end{spec}
 denotational semantics
 
\subsection{Syntax}
 Figure ~\ref{syntax} gives the syntax for Mini-ML.
 
This section presents the syntax and semantics of \name.
 
\begin{figure}
\begin{spec}
seval :: Expr () ExecutionTree -> ExecutionTree
seval (x)  =   x
seval (c)  =   c
seval (e1 op e2)  =  merge op (seval e1) (seval e2)
seval (Lam n t f)  =  Exp $ SFun n (seval . f) t
seval (Let x e f)  =  seval . f $ seval e
seval (App e1 e2)  =  treeApply (seval e1) (seval e2)
seval (BLam a f)  =  seval $ f a
seval (TApp e t)  =  seval e
seval (LetRec _ _ binds body)  =  seval . body . fix $ map seval . binds
seval (Data _ _ e)  =  seval e
seval (Constr c es)  = mergeList (Constr (map seval es))
seval (case e of [ConstrAlt xs e]) = propagate (seval e) (map (seval . f) alts)
\end{spec}
\caption{Denotational semantics for symbolic execution}
\label{seval}
\end{figure}
 
 Auxilary functions:
 
\begin{spec}
mergeList ::  ([SymValue] -> SymValue) -> [ExecutionTree] -> ExecutionTree
mergeList f []                           =  f []
mergeList f (v : vs)                     =  mergeList (\es -> f (v:es)) vs
mergeList f (Fork dt e ts : xs)          =  Fork dt e [(c, ns, \es -> mergeList f (g es : xs)) | (c,ns,g) <- ts]
\end{spec}

\begin{spec}
merge :: (SymValue -> SymValue -> SymValue) -> ExecutionTree -> ExecutionTree -> ExecutionTree
merge op s1 s2 = Exp (op s1 s2)
merge op (Fork dt e ts) t = Fork dt e [(c, ns, \es -> merge op (g es) t) | (c,ns,g) <- ts]
merge op t (Fork dt e ts) = Fork dt e [(c, ns, merge op t . g) | (c,ns,g) <- ts]


treeApply :: ExecutionTree -> ExecutionTree -> ExecutionTree
treeApply (Exp e) t =
    case e of
      SVar n i typ -> apply (SApp (SVar n i typ)) t
      SFun _ f _ -> f t
treeApply (Fork dt e ts) t = Fork dt e [(c, ns, \es -> treeApply (f es) t) | (c,ns,f) <- ts]

apply :: (SymValue -> SymValue) -> ExecutionTree -> ExecutionTree
apply f (Exp e) = Exp (f e)
apply f (Fork dt e ts) = Fork dt e [(c, ns, apply f . g)| (c,ns,g) <- ts]

propagate :: ExecutionTree
          -> [(SConstructor, [S.ReaderId], [ExecutionTree] -> ExecutionTree)]
          -> ExecutionTree
propagate (Exp e) t = Fork e t
propagate (Fork e t1) t2 = Fork e [C \es -> propagate f (es) t2]
 

exec :: ExecutionTree -> (ExecutionTree, Int)
exec = go 0
    where go i (Exp (SFun n f t)) =
              case go (i+1) (f . Exp $ SVar n i t) of
                (e', i') -> (NewSymVar i t e', i')
          go i e = (e, i)
\end{spec}

What \texttt{merge} and \texttt{mergelist does}

\begin{comment}
\end{comment}




\subsection{Syntax}

Figure~\ref{f:syntax} shows the the core syntax of a typical functional language.

Some notes
- $\texttt{if}\;e_1\;e_2\;e_3$ will be desugared to $\texttt{case}\;e_1\;\texttt{of}\;[True\arrow e_2, False\arrow e_3]$

- $e_1 \Longrightarrow e_2$ will be desugared to $\texttt{case}\;e_1\;\texttt{of}\;[True\arrow e_2]$

- Pattern matching should be exhausted

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

  (\texttt{Prm}) &
\myirule{
           \rho, e_i \Downarrow v_i
 }{
           \rho,C\!/\!o~\overline{e} \Downarrow C\!/\!o~\overline{v}
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
\multicolumn{2}{l}{\myruleform{\sigma,e\Downarrow_s t}} \\ \\

  (\texttt{Var}) &
\myirule{}{
            \sigma,x \Downarrow_s \sigma(x)
} \\ \\

  (\texttt{Lit}) &
\myirule{}{
            \sigma,c \Downarrow_s c
} \\ \\

%  (\texttt{Con}) &
%\myirule{          \sigma, e_i \Downarrow t_i \;\;\;
%                   C~\overline{t}\Downarrow t

%}{
%            \sigma,C~\overline{e} \Downarrow t} \\ \\

  (\texttt{Prm}) &
\myirule{          \sigma, e_i \Downarrow_s t_i \;\;\;
                   (C\!/\!o,\overline{t})\Downarrow_o t

}{
            \sigma,C\!/\!o~\overline{e} \Downarrow_s t} \\ \\

  (\texttt{Lam}) &
\myirule{

}{
           \sigma, \lambda x . e \Downarrow_s \langle\lambda x.e,\sigma\rangle
} \\ \\

  (\texttt{Let}) &
\myirule{
           \sigma, e_1 \Downarrow_s t_1 \;\;\;
           \sigma [f\mapsto t_1], e_2 \Downarrow_s t
 }{
           \sigma,\texttt{let}\;f = e_1\;\texttt{in}\;e_2\Downarrow_s t
} \\ \\


%  (\texttt{Con}) &
%\myirule{
%}{
%            \sigma,C_n \Downarrow \lambda \alpha_1 \ldots \lambda \alpha_n .~C_n~\overline{\alpha}
%} \\ \\

  (\texttt{App}) &
\myirule{
           \sigma, e_1 \Downarrow_s t_1\;\;\; \sigma, e_2 \Downarrow_s t_2\\
           (t_1,t_2) \Downarrow_a t
 }{
           \sigma,e_1\;e_2 \Downarrow_s t
} \\ \\



  (\texttt{Cas}) &
\myirule{
           \sigma, e \Downarrow_s t_1 \\
         %%  \rho_i = match\; v\; p_i\;\;\;
           \sigma[\overline{x} \mapsto \overline{a}],e_i\Downarrow_s t_i \\
           (t_1,[C_i~\overline{a} \arrow t_i]_{i\in I}) \Downarrow_c t
 }{
           \sigma,\texttt{case}\;e\;\texttt{of}\;[C_i~\overline{x}\arrow e_i]_{i\in I} \Downarrow_s t
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


\figtwocol{f:approx}{Approximation Rules}{
\small
\bda{l}

\textbf{}
\\ \\

\ba{lc}
\multicolumn{2}{l}{\myruleform{t\apx v}} \\ \\

 &
\myirule{}{
            c\apx c
} \\ \\

&
\myirule{}{
            a\apx v
} \\ \\

&
\myirule{}{
            \langle\lambda x . e,\sigma\rangle \apx \langle\lambda x . e,\rho\rangle
} \\ \\

&
\myirule{\overline{s\apx v}}{
            C\!/\!o~\overline{s}\apx C\!/\!o~\overline{v}} \\ \\

&
\myirule{}{
            a~s\apx v
} \\ \\

&
\myirule{}{
            \texttt{case}\;s\;\texttt{of}\;[C_i~\overline{a}\arrow t_i]_{i\in I}\apx ?
} \\ \\

\ea

\eda
}
\begin{theorem}[Correctness of Symbolic Execution]
For all e, giving $\rho$ and $\sigma$ such that $\sigma\apx\rho$, if $\rho,e\Downarrow v$ and $\sigma,e\Downarrow_s t$ then $t\apx v$.
\end{theorem}
Prove by case analysis on the derivation of $\rho,e\Downarrow v$ and induction on $e$.
