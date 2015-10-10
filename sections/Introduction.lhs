\section{Introduction}\label{sec:intro}

> prop_if    ::  Int32 -> Bool
> prop_if x  =  if x == 123 then False else True
 
Property-based testing (PBT) has established itself as an important
tool for testing functional programs.  The existing approaches to PBT
use for the most part random testing.

In imperative programming random testing has also been widely
used. However, several authors have argued against the drawbacks
of random testing, while promoting other approaches, such as Symbolic Execution.
Symbolic execution is interesting for testing because a program path can
be followed, not only for a concrete input, but for all inputs that satisfy
the path condition. In random testing, due to the use of a concrete input,

Symbolic execution seems a very good fit for functional programming.

Property-based testing is by now a well-established mechanism for testing FP programs;
Property-based testing is usually done using random testing;
In Imperative programming, several researchers have pointed flaws to random testing;
Alternatives include among others, Symbolic Evaluation
Benefits of SE: can follow a path symbolically, without concrete values
SE seems a perfect fit for FP:
  * FP has no side-effects, which are difficult to deal with in SE
  * FP often defines programs by pattern matching, when the input size for each path tends to be quite big
paths with large input sizes benefit from SE
* SE combined with property-based testing can improve significantly the coverage, for programs that have such large paths

so the additional thing in FP is higher-order values
which is what the Racket guys have been emphasizing and exploring as well
that should set us apart from Imperative Programming
right
and, hopefully, Property-based Testing + FP with datatypes
should set us apart from the Racket guys

so, in SE the branching constructs are obviously the most intersting aspects
but there is a big gap in expressiveness between a simple "if"
and case analysis
case analysis introduces binding, for example

Large Paths + Parametric definitions + White Box Testing
