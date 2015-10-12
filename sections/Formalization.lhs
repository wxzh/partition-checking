%format (seval (x)) = "\mathcal{E} \llbracket " x "\rrbracket "
%format merge  = "\mathcal{M} "
%%format (Lam n t f) = "\lambda (x:\tau).e"
%%format (BLam a f) = "\Lambda \alpha.e"
%%format (Let x e1 e2) = "\texttt{let } x=" e1 " \texttt{ in } " e2
%%format (App e1 e2) = "e_1\;e_2"
%%format (TApp e1 e2) = "e\;\tau"
 
%format ADD = +
%format SUB = -
%format MUL = *
%format DIV = /
%format LT = <
%format LE = "\leqslant"
%format GT = >
%format GE = "\geq"
%format EQ = "\equiv"
%format NEQ = "\not\equiv"
%format OR = "\lor"
%format AND = "\land"
 
%format e1 = "e_1"
%format e2 = "e_2"
%format es = "\overline{e}"
 
%format ExecutionTree = "\mathcal{T} "
%format Leaf = "\mathcal{L} "
%format Fork = "\mathcal{F} "
 
\section{Formalisation}\label{sec:formal}

\subsection{Syntax}
Figure ~\ref{fig:syntax} gives the syntax for Mini-ML. We encode it using parametric higher-order abstract syntax(PHOAS)~\cite{}.
Note that ``$\texttt{if}\;e1\;e2\;e3$" and ``$e_1 \Longrightarrow e_2$" are not part of it because they can be treated as the syntatic sugar of \texttt{case} expressions:
the former can be desugared to to be ``$\texttt{case}\;e_1\;\texttt{of}\;[True\arrow e_2, False\arrow e_3]$";
the latter can be  will be desugared to ``$\texttt{case}\;e_1\;\texttt{of}\;[True\arrow e_2]$".

% Pattern matching should be exhausted
 
\begin{figure}
\begin{spec}
data Expr a
  = Int Integer                                   -- integer
  | Bool Bool                                     -- boolean
  | Var a                                         -- variable
  | PrimOp (Expr a) Op (Expr a)                   -- binary operation
  | Lam Type (a -> Expr a)                        -- abstraction
  | App (Expr a) (Expr a)                         -- application
  | Let (Expr a) (a -> Expr a)                    -- let binding
  | Case (Expr a) [(Constructor, [a] -> Expr a)]  -- pattern matching
  | Constr Constructor [Expr a]                   -- constructor application
  | BLam String Expr                              -- type abastraction
  | TApp Expr Type                                -- type application
 
data Op = ADD | SUB | MUL | DIV | LT | LE | GT | GE | EQ | NEQ | OR | AND

data Value
  = VVar Int
  | VInt Integer
  | VBool Bool
  | VApp Value Value
  | VFun (ExecutionTree -> ExecutionTree) Type
  | VConstr Constructor [Value]
 
data ExecutionTree = Leaf Value | Fork Value [(Constructor, [ExecutionTree] -> ExecutionTree)]
\end{spec}
\caption{Syntax of Mini-ML}
\label{fig:syntax}
\end{figure}
 
 
\subsection{Semantics}
Figure~\ref{fig:seval} shows the semantics of symbolic execution.

\begin{figure}
\begin{spec}
seval :: Expr ExecutionTree -> ExecutionTree
seval (Int i)            =  Leaf $ VInt i
seval (Bool b)           =  Leaf $ VBool b
seval (Var x)            =  x
seval (PrimOp e1 op e2)  =  merge (lift op) [seval e1, seval e2]
seval (Lam t f)          =  Leaf $ VFun (seval . f) t
seval (App e1 e2)        =  treeApply (seval e1) (seval e2)
seval (Let e f)          =  seval . f $ seval e
seval (Constr c es)      =  merge (VConstr c) $ map seval es
seval (Case e alts)      =  propagate (seval e) [(c, seval . f) | (c, f) <- alts]
\end{spec}
\caption{Semantics of symbolic execution}
\label{fig:seval}
\end{figure}

\subsection{Auxilary Functions}
\begin{spec}
treeApply :: ExecutionTree -> ExecutionTree -> ExecutionTree
treeApply (Leaf (VVar n)) t = apply (VApp (VVar n)) t
treeApply (Leaf (VFun f)) t = f t

apply :: (Value -> Value) -> ExecutionTree -> ExecutionTree
apply f (Leaf v)     =  Leaf (f v)
apply f (Fork v bs)  =  Fork v [(c, apply f . g) | (c, g) <- bs]

-- propagate the condition
propagate :: ExecutionTree -> [(Constructor, [ExecutionTree] -> ExecutionTree)] -> ExecutionTree
propagate (Leaf e) bs      =  Fork e bs
propagate (Fork e bs) bs'  =  Fork e [(c, \es -> propagate (g es) bs') | (c, g) <- bs]

-- apply function f to the tree
merge :: ([Value] -> Value) -> [ExecutionTree] -> ExecutionTree
merge f []                =  Leaf $ f []
merge f ((Leaf v):ts)     =  merge (\ts -> f (v:ts)) ts
merge f ((Fork v bs):ts)  =  Fork v [(c, \es -> merge f (g es : ts)) | (c, g) <- bs]

lift :: Op -> [Value] -> Value
lift op vs =
  case (v1, v2) of
   (VInt i1, VInt i2) ->
     case op of
      ADD  ->  VInt (i1 + i2)
      SUB  ->  VInt (i1 - i2)
      MUL  ->  VInt (i1 * i2)
      DIV  ->  VInt (i1 `div` i2)
      GT   ->  VBool (i1 > i2)
      LT   ->  VBool (i1 < i2)
      GE   ->  VBool (i1 >= i2)
      LE   ->  VBool (i1 <= i2)
      EQ   ->  VBool (i1 == i2)
      NEQ  ->  VBool (i1 /= i2)
   (VBool b1, VBool b2) ->
     case op of
      EQ   ->  VBool (b1 == b2)
      NEQ  ->  VBool (b1 /= b2)
      AND  ->  VBool (b1 && b2)
      OR   ->  VBool (b1 || b2)
  where
    v1 = vs !! 0
    v2 = vs !! 1
\end{spec}


Visualise what \texttt{merge} does

\begin{comment}
\end{comment}





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
