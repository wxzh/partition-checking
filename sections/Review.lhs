\section{A Recap of QuickCheck}
In this section, we will illustrate the limitations of \qc through a couple of examples.
 
\subsection{A Running Example}
 
Suppose that we would like to test an implemention of the data structure AVL trees (a.k.a. self-balancing binary search trees) in Haskell\footnote{Inspired by the blog post~\url{http://matt.might.net/articles/quick-quickcheck/}}.

an AVL tree is a \emph{binary search tree} as well as \emph{balanced tree}, it derives the properties from both:
 
\begin{itemize}
  \item \emph{Binary search tree}: the value in the parent node must be greater than all values in the left child, and smaller than all values in the right child.
  \item \emph{Balanced tree}: for any node, the heights of its left and right child  differ by at most one.
%  \item all values stored in the node should be distinct
 \end{itemize}

The datatype definition of AVL trees is given:

> data Tree = Leaf | Node Int Tree Tree

The function under test is \emph{insert} which has the following signature:

> insert :: Tree -> Int -> Tree
 
The specification of \texttt{insert} states that it takes an AVL tree and an integer value and returns a new AVL tree with the value inserted into the appropriate position of the given tree.
 
To reveal the invariant of the \texttt{insert} function, one could write the property below:
 
> prop_insert      ::  Tree -> Int -> Bool
> prop_insert t i  =   isAvlTree t ==> isAvlTree (insert t i)
 
which is a straightforward mapping from the specification where we use the conditional property to state that the tree is an AVL tree before and after insertion.
 
The definition of \texttt{isAvlTree} is as follows:

% Due to the limitation of the space, we omit their definitions here.
 
> isSearchTree                                          ::  Tree -> Bool
> isSearchTree (Node i l@(Node j _ _) Leaf)             =   i > j && isSearchTree l
> isSearchTree (Node i Leaf r@(Node j _ _))             =   i < j && isSearchTree r
> isSearchTree (Node i l@(Node j _ _) r@(Node k _ _))   =   j < i && i < k && isSearchTree l && isSearchTree r
> isSearchTree _                                        =   True
>
> isBalancedTree                ::  Tree -> Bool
> isBalancedTree  Leaf          =   True
> isBalancedTree  (Node i l r)  =   difference <= 1 && isBalancedTree l && isBalancedTree r
>    where difference  =  abs $ height l - height r
>
> height               ::  Tree -> Int
> height Leaf          =  0
> height (Node _ l r)  =  1 + height l `max` height r
>
> isAvlTree  ::  Tree -> Bool
> isAvlTree  =  isSearchTree t && isBalancedTree t

%Assume that \texttt{insert} has already been defined and we would like to check the correctness of its implementation via the above property.

\subsection{Generators}
 
\paragraph {A Naive Generator} \qc generates test data according to its type.
Since \texttt{Tree} is a self-defined type which does not have a default generator,
we have to define one manually through declaring \texttt{Tree} as an instance of \texttt{Arbitrary} type class with the \texttt{arbitrary} hook method implemented.
Below is what a casual user may define:

> instance Arbitrary Tree where
>   arbitrary = oneof [return Leaf, liftM2 arbitrary arbitrary]

If we do \texttt{sample (arbitrary :: Gen Tree)} using this generator, we will see that what it generates are usually either too simple(just \texttt{Leaf}) or too complicated.
It may not even terminate in the worst case!

\paragraph {A Revised Generator} To generate trees with a reasonable size and achieve a more uniform distribution of the test data,
a more experienced user who knows the \qc library well may write:
 
> arbitrary = sized arbTree
>   where arbTree 0         = return Leaf
>         arbTree n | n > 0 = frequency
>                          [ (1, return Leaf)
>                          , (4, liftM3 Node arbitrary tree tree) ]
>                where tree = arbTree $ n `div` 2

In here, the \texttt{sized} combinator guarantees the termination of generation and by lowering the probability of selecting \texttt{Leaf} as the constructor from 50\% to 20\% through \texttt{frequency}.
If we run \texttt{quickCheck prop\_insert} again, what we will see is ``+++ OK, passed 100 tests." It seems that this modification works well but in fact not.
If use \texttt{verboseCheck} to look deep inside the process, substantial cases generated indeed do not satisfy the condition.
This is because what the generator produces are arbitrary binary trees and the chance that they happen to be AVL trees is extremely low.
However, all the discarded cases would be counted into the total number of test cases, meaning that only a few cases are actually exercised,
which may reduce the our confidence about the test result.

\paragraph{The Final Generator} We had better not use conditional properties for the rarely satisfiable conditions.
Instead, the precondition in the property should be moved to the \emph{custom generators} to generate valid test cases in the first place.
 
> prop_insert     ::  Tree -> Int -> Bool
> prop_insert t i =  isAvlTree (insert t i)

The first try is to use \texttt{insert}, the function under test, inside the generator:

> instance Arbitrary Tree where
>   arbitrary = liftM (foldl insert Leaf) arbitrary

However, \texttt{insert} is not trust-worthy. Then, a natural idea is to implement \texttt{insert} of our own inside the generator.
This option has several issues: (1) we need to write more code (2) the semantics of the generator should be kept in sync with \texttt{insert}, which will result in maintainess problem (3) the generator becomes so complicated that its correctness should be also verified by additional test code~\cite{palka2011testing}.
 
In summary,
- Conditional properties is the natural way to write \emph{declarative} properties but they are risky.
- Custom generators of good quality are hard to define.
 
The complexity of hand-written generators inspires the works on automatically derive generators~\cite{claessen2014generating,lampropoulosmaking}.
 
\subsection{Shrinking}
\qc will report counterexamples if the function under test or the property itself is errorneous. For example, the \texttt{insert} simply returns the original AVL tree:
 
> insert :: Tree -> Int -> Tree
> insert t _ = t
 
However, the counterexample it reports is often:
 
% a complex counterexample here
> Node (-5) (Node (-18) (Node (-19) Leaf Leaf) (Node (-7) (Node (-17) Leaf Leaf) Leaf)) (Node 18 (Node 4 Leaf (Node 13 Leaf Leaf)) Leaf)
> 0

The counterexample might not be so useful since it is too complex to give users the intuition about the source of the bug.
\texttt{Arbitrary} type class exposes an interface called \texttt{shrink} for minimizing the counterexample.
The mechanism of shrinking is to recursively try all possible smaller values, if any of them can also falsify the property, \qc will continue shrinking.
If none, the counterexample is considered as minimal and reported.

In the past, users had to manually implement it for self-defined algebraic datatypes. For example, the standard way for shrinking trees:
 
> shrink Leaf          =  []
> shrink (Node i l r)  =  [Leaf] ++ [l, r] ++ [Node i' l' r' | (i', l', r') <- shrink (i, l, r)]
 
With the help of GHC generics recent version of \qc provides an efficient generic shrink for algebraic datatypes.
We can now simply define it as:

> shrink x = shrinkToLeaf x ++ genericShrink x
>   where shrinkToLeaf Leaf  =  []
>         shrinkToLeaf _     =  [Leaf]

which has the similar effect as manually written version while eliminates the boilerplate code for most cases.
Nonetheless, it might not be applicable to all situations.
 
The ideal shrinking for AVL trees should enumerate all AVL trees than the original AVL tree. However, the default shrinking for \texttt{Tree}
would produce a large number of trees that are indeed not AVL trees because it shrinks the value stored in the \texttt{Node} which may break the invariant of \emph{binary search tree}
and shrinks on one child while keeps the another child which may break the invariant of \emph{balanced tree}.
As a result, the execution time is wasted on these smaller values or the counterexample shrunk is wrong.
In the worst case the number of distinct smaller values may intractable for QuickCheck to analyse~\cite{pike2014smartcheck}.
 
Of course users can provide their own \emph{efficient} shrinking implementation, which is again, not trival~\cite{pike2014smartcheck}.
 
% The drawback of shrinking retains. The number of smaller values may be untractable which the may take significant time to inspect these instances one by one especially when the original counterexample is already minimal. In the worst case, nothing will be shrunk.

\subsection{Bugs That \qc Can Hardly Find}

\begin{comment}
> balanceFactor               ::  Tree -> Int
> balanceFactor (Node _ l r)  =   height l - height r
> balanceFactor _             =   0
>
> balance        ::  Tree -> Tree
> balance Leaf   =  Leaf
> balance t@(Node _ l r)
>   | diff > 1   =  if balanceFactor l > 0 then rotateLL t else rotateLR t
>   | diff < -1  =  if balanceFactor r < 0 then rotateRR t else rotateRL t
>   | otherwise  =  t
>   where diff   =  balanceFactor t
>
> rotateLL, rotateRR, rotateLR, rotateRL               ::  Tree -> Tree
> rotateLL (Node i (Node i' l' r') r)                  =  Node i' l' (Node i r' r)
> rotateRR (Node i l (Node i' l' r'))                  =  Node i' (Node i l l') r'
> rotateLR (Node i (Node i' l' (Node i'' l'' r'')) r)  =  Node i'' (Node i' l' l'') (Node i r'' r)
> rotateRL (Node i l (Node i' (Node i'' l'' r'') r'))  =  Node i'' (Node i l l'') (Node i' r'' r')
>
> insert           ::  Tree -> Int -> Tree
> insert Leaf i    =  Node i Leaf Leaf
> insert t@(Node v l r) i
>     | i > v      =  balance $ Node v l (insert r i)
>     | i < v      =  balance $ Node v (insert l i) r
>     | otherwise  =  t
\end{comment}

% We expect that \qc will capture the bug for us, but unfortunately, it can hardly report a counterexample. The reason is that ...

There exists a class of programs that \qc suffers from finding bugs, i.e. \emph{only a small portion of the input space can trigger the bug}.
It is indeed a common problem of black-box testing strategy since the probability of test cases generated happens to fall into that portion is extremely low.
 
Recall the example we show in Section~\ref{intro} which is a representative of programs of this kind.
 
\subsection{Polymorphic Properties}

We need to define polymorphic properties for polymorphic functions.
 
> prop_ReverseAppend :: Eq a => [a] -> [a] -> Bool
> prop_ReverseAppend xs ys = reverse (xs ++ ys) == reverse xs ++ reverse ys

%which is a wrong property on \texttt{reverse} and
This property is apparently wrong: the occurrences of \texttt{xs} and \texttt{ys} should be swapped.
 
A simple counter-example could be $xs = [0]$ $ys = [1]$: \texttt{reverse ([0] ++ [1])} returns \texttt{[1,0]} while \texttt{reverse [0] ++ reverse [1]} returns \texttt{[0,1]}.
However, no matter how many times we \qc this property, we will always see ``+++ OK, passed 100 tests.".
The reason is that to generate test inputs, \qc has to instantiate the polymorphic type with a concrete type which is \texttt{()}(unit) by default.
Nonetheless, the unit type can not capture any difference in the content of the lists.

Recent version of \qc exposes interfaces like \texttt{polyQuickCheck} which defaults type variables to \texttt{Integer} making the property sound.
 
A more appropriate solution is to construct a specialised monomorphic type by inspecting the type signature such that testing the property on this type is enough~\cite{bernardy2010testing}.

\subsection{Higher-order Properties}

Higher-order functions play a prominent role in functional programming. To test them, we may write higher-order properties that take functions as arguments.
Here is an artificial property:

> prop_function :: (Int -> Int) -> Bool
> prop_function f = not (f 0 == 123)
 
Every function that takes 0 and returns 123 will make this property fail.
But if we try to run the property, we will encounter a problem:

\begin{lstlisting}[language=lisp]
GHCi> quickCheck prop_function
Error: No instance for (Show (Int -> Int)) arising from a use of ‘quickCheck’
\end{lstlisting}

\qc can somehow generate functions at random but it is not able to display the functional values since function type is not an instance of \texttt{Show}.
Simply importing \texttt{Text.Show.Functions} will not work because no information about the counterexample will be displayed except the placeholder \texttt{"<function>"}.
% Functions may be infinite and thus they are hard to convert into a String

Claessen~\cite{claessen2012shrinking} proposes a way of showing and shrinking functions and it has been integrated into \qc, which requires users to wrap and unwrap around functional values.

> prop_function :: Fun Int Bool -> Bool
> prop_function f = not ((apply f) 0 == 123)

This improvement can catch bugs sometimes, but it is not the case for this example. Why?
This program is also a variant of the class of programs that \qc suffers from finding bugs we discussed in the previous section.

\subsection{The Limitations of \qc}

From the example we can conclude that in \qc, the effectness of testing heavily depends on the quality of the test generator and shrinking function. However, writing them is arduous and hard, which requires a good understanding of the \qc library, the mechanism under the hood and the program under test. On the contrary, in \name, no generators and shrinking functions is needed which eases property-based testing.
We summarise the limitations of \qc below:

% \begin{enumerate}

Having the \qc can effectively find bugs for most cases. However, restricted by the nature of random testing, \qc has difficulty finding bugs that only a small portion of inputs can trigger

% \qc black-box but users do white-box manually, contradiction.

\begin{enumerate}
\item \emph{ Manually defined generators for algebraic datatypes. } \qc adopts type-directed approach to generate test data requiring the type to be an instance of \texttt{Arbitrary} type class with the hook method \texttt{arbitrary} implemented. Though \qc  generators for commonly used types and a set of combinators for defining generators, it is still bothersome and tricky to implement generators for self-defined algebraic datatypes.

\item \emph{ Hard to define generators which generates test data of good quality. }
The effectiveness of random testing to a large extent depends on the quality of
test data generated. Writing a generator which can deterministically generates
reasonable size data and achieve approapriate distribution can be extremely subtle. What worse is that if there exists some flaw in the generator, \qc may never find the bug.

\item \emph{ No guarantee for the minimalism of the counterexample reported. } Small counterexample will ease the process of debugging. \qc is shipped with a mechanism called \emph{shrinking}, which iteratively uses smaller values derived from the original one to falsify the property. "Without it [shrinking], randomly generated failing cases would often be so large as to be almost useless." as Hughes said.

 However, defining an efficient shrinking method manually is hard if one does not understand the shrinking well.

\item \emph{ Low test coverage. } Due to the nature of randomness, test coverage of \qc can not be measured precisely. Typically 100 (by default) randomly generated test cases would be exercised, which merely occupies a small portion of the input space.
\end{enumerate}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
