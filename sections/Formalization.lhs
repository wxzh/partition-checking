%%%%%  Functions %%%%%
%format (seval (x)) = "\mathcal{E} \llbracket " x "\rrbracket "
%format merge  = "\mathcal{M} "
%format (subst x v) = "\rho[" x "\mapsto" v "]"
 
%%%%%  Expressions %%%%%
%format (Expr a) = e
%format (Int a) = a
%format (Lam n t f) = "\lambda (x:\tau).e"
%format (BLam a f) = "\Lambda \alpha.e"
%format (Let e f) = "\texttt{let}\;x=e_1\;\texttt{in}\;e_2"
%format (LetRec es e) = "\texttt{let rec}\;\overline{x=e}\;\texttt{in}\;e"
%format (App e1 e2) = e1 "\;" e2
%format (PrimOp e1 op e2) = e1 "\;" op "\;" e2
%format (TApp e1 e2) = "e\;\tau"
%format (Case e alts) = "\texttt{case}\;e\;\texttt{of}\;\overline{C\;\overline{x}\rightarrow e}"
%format (Constr c es) = "C\;\overline{e}"
%format (Boolean a) = b
%format (Var a) = x

%%%%% Values %%%%%
%format (VInt a) = a
%format (VBool a) = a
%format (VVar a) = "a_I"
%format (VApp a b) = a "\;" b
%format (VFun f t) = "\langle \lambda (x:\tau.e), \rho \rangle"
%format (VConstr c vs) = "C\;\overline{v}"
%format (Constructor c) = C
%format (VOp v1 op v2) = v1 "\;" op "\;" v2

%%%%% Types %%%%%
%format Type = "\tau"
%format TInt = "Integer"
%format TBool = "Boolean"
%format TFun x y = "\overline{\tau} \rightarrow \tau"
%format TData n = D
 
%format Value = v
%format Integer = i
%format Bool = b
 
%%%%% Operators %%%%%
%format Op = "op"
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
 
%%%%% Variables %%%%%
%format e1 = "e_1"
%format e2 = "e_2"
%format v1 = "v_1"
%format v2 = "v_2"
%format i1 = "i_1"
%format i2 = "i_2"
%format b1 = "b_1"
%format b2 = "b_2"
%format es = "\overline{e}"
 
%%%%% Execution trees %%%%%
%format ExecutionTree = "\mathcal{T} "
%format Leaf = "\mathcal{L} "
%format Fork = "\mathcal{F} "
%format p = "\rho"
 
 
\section{Formalisation}\label{sec:formal}

\subsection{Syntax}
Figure~\ref{fig:syntax} gives the syntax for Mini-ML. We use parametric higher-order abstract syntax(PHOAS)~\cite{} to encode it in our implementation.
 
Note that ``$\texttt{if}\;e_1\;e_2\;e_3$" and ``$e_1 \Longrightarrow e_2$" are omitted because they can be treated as the syntatic sugar of \texttt{case} expressions:
the former can be desugared to to be ``$\texttt{case}\;e_1\;\texttt{of}\;[True\arrow e_2, False\arrow e_3]$";
the latter can be desugared to ``$\texttt{case}\;e_1\;\texttt{of}\;[True\arrow e_2]$".

% Pattern matching should be exhausted
 
\begin{figure}
\begin{spec}
data Expr a
  =  Int Integer                                   -- integer
  |  Boolean Bool                                  -- boolean
  |  Var a                                         -- variable
  |  PrimOp (Expr a) Op (Expr a)                   -- binary operation
  |  Lam Type (a -> Expr a)                        -- abstraction
  |  App (Expr a) (Expr a)                         -- application
  |  Let (Expr a) (a -> Expr a)                    -- let binding
  |  LetRec ([a] -> [Expr a]) ([a] -> Expr a)      -- let rec
  |  Case (Expr a) [(Constructor, [a] -> Expr a)]  -- pattern matching
  |  Constr Constructor [Expr a]                   -- constructor application
  |  BLam Expr                                     -- type abastraction
  |  TApp Expr Type                                -- type application
 
data Op = ADD | SUB | MUL | DIV | LT | LE | GT | GE | EQ | NEQ | OR | AND

data Value
  =  VVar Int Type
  |  VInt Integer
  |  VBool Bool
  |  VApp Value Value
  |  VFun (ExecutionTree -> ExecutionTree) Type
  |  VOp Value Op Value
  |  VConstr Constructor [Value]
 
data Type
  =  TInt
  |  TBool
  |  TFun [Type] Type
  |  TData String
 
data ExecutionTree = Leaf Value | Fork Value [(Constructor, [ExecutionTree] -> ExecutionTree)]

p :: x -> ExecutionTree -- environment that maps variables to execution trees
 
\end{spec}
\caption{Syntax of Mini-ML}
\label{fig:syntax}
\end{figure}
 
\subsection{Semantics}
Figure~\ref{fig:seval} shows the semantics of symbolic execution.

\begin{figure}
\begin{spec}
seval :: Expr ExecutionTree -> p -> ExecutionTree
seval (Int i) p            =  Leaf (VInt i)
seval (Bool b) p           =  Leaf (VBool b)
seval (Var x) p            =  p(x)
seval (PrimOp e1 op e2) p  =  merge (lift op) [seval e1 p, seval e2 p]
seval (Lam t f) p          =  Leaf $ VFun (seval . f) t
seval (App e1 e2) p        =  treeApply (seval e1 p) (seval e2 p)
seval (Let e1 e2) p        =  seval e2 (subst x (seval e1 p))
seval (LetRec fs f) p      =  seval . f . fix $ map seval . fs
seval (Constr c es) p      =  merge (VConstr c) $ map seval es
seval (Case e alts) p      =  propagate (seval e p) map [(c, seval alt p) | (c, f) <- alts]
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
propagate (Leaf v) bs      =  Fork v bs
propagate (Fork v bs) bs'  =  Fork v [(c, \ts -> propagate (g ts) bs') | (c, g) <- bs]

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
   _ -> VOp v1 op v2
  where
    v1 = vs !! 0
    v2 = vs !! 1
\end{spec}

\begin{comment}
seval :: Expr ExecutionTree -> ExecutionTree
seval (Int i)            =  Leaf (VInt i)
seval (Bool b)           =  Leaf (VBool b)
seval (Var x)            =  x
seval (PrimOp e1 op e2)  =  merge (lift op) [seval e1 po, seval e2 po]
seval (Lam t f)          =  Leaf $ VFun (seval . f) t
seval (App e1 e2)        =  treeApply (seval e1) (seval e2)
seval (Let e f)          =  seval $ f (seval e)
seval (LetRec fs f)      =  seval . fs . fix $ map seval . f
seval (Constr c es)      =  merge (VConstr c) $ map seval es
seval (Case e alts)      =  propagate (seval e) [(c, seval . f) (c, f) <- alts]
\end{comment}


Visualise what \texttt{merge} does

\begin{comment}
\end{comment}




\figtwocol{f:syntax}{Abstract Syntax}{
\small
\bda{l}

\ba{llrl}
    \textbf{Expressions} & e & ::=  & x \mid c \mid C~\overline{e}\mid o~\overline{e} \mid
                         \lambda (x:\tau) . e \mid e_1\;e_2 \mid \Lambda \alpha .e \mid e\;\tau \mid\\
                         &&&\texttt{let}\;f = \lambda (x:\tau) . e_1\;\texttt{in}\;e_2 \mid \\
                         &&&\texttt{data}\;d\;\overline{\alpha} = \overline{C_i~\overline{\tau}}\;\texttt{in}\;e \mid \texttt{case}\;e\;\texttt{of}\;[C_i~\overline{x}\arrow e_i]_{i\in I} \\
    \textbf{Types} & \tau & ::= & \alpha \mid Int \mid Bool \mid d \mid {\tau}_1 \arrow {\tau}_2 \mid \forall \alpha. \tau\\
    \textbf{Symbolic Values} & s & ::= & a \mid c \mid \langle\lambda (x:\tau) . e,\sigma\rangle \mid \langle\Lambda \alpha . e,\sigma\rangle \mid C~\overline{s} \mid o~\overline{s} \mid a\;s  \\
    \textbf{Execution Trees} & t & ::= & s \mid \texttt{case}\;s\;\texttt{of}\;[C_i~\overline{a}\arrow t_i]_{i\in I} \\ %\mid \forall a.t\\
 
 \\
    \textbf{SMT Program} & p & ::=  & \overline{stmt} \\
    \textbf{SMT Statements} & stmt & ::=  & (\texttt{declare-datatypes}\;()\;((D\;(\overline{C_i~\overline{x_j\;\tau}}))) \mid \\
                                   &&&  (\texttt{declare-const}\;x\;\tau) \mid (\texttt{declare-fun}\;x\;(\overline{\tau})\;\tau) \mid \\
                                   &&& (\texttt{assert}\;e) \mid (\texttt{check-sat}) \mid (\texttt{push}) \mid (\texttt{pop}) \\
    \textbf{SMT Expressions} & e & ::=  & x \mid c \mid (C~\overline{e}) \mid (o~\overline{e}) \mid (e_1\;e_2)\\
    \textbf{SMT Types} & \tau & ::= & Int \mid Bool \mid D \\

\ea
\\ \\

\ba{llrl}
\textbf{SMT Environments} & \omega & ::= & \epsilon \mid \omega[a\mapsto x_i]
\ea
\\ \\
\eda
}

\figtwocol{f:semantics}{Symbolic Operational Semantics}{
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
