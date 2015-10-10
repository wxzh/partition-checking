% page: 25
\documentclass[runningheads,a4paper]{llncs}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

\usepackage{amsmath}
%\usepackage[retainorgcmds]{IEEEtrantools}
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
\usepackage{qtree}
\usepackage{xspace}
\usepackage{listings}
\usepackage{comment}
%\usepackage{mylhs2tex}
 
\usepackage{tabularx}
\usepackage[para,online,flushleft]{threeparttable}
 
%\usepackage{subfig}
 
\lstset{ %
language=Haskell,                % choose the language of the code
columns=flexible,
lineskip=-1pt,
basicstyle=\ttfamily\small,       % the size of the fonts that are used for the code
%numbers=none,                   % where to put the line-numbers
numberstyle=\ttfamily\tiny,      % the size of the fonts that are used for the line-numbers
stepnumber=1,                   % the step between two line-numbers. If it's 1 each line will be numbered
numbersep=5pt,                  % how far the line-numbers are from the code
backgroundcolor=\color{white},  % choose the background color. You must add \usepackage{color}
showspaces=false,               % show spaces adding particular underscores
showstringspaces=false,         % underline spaces within strings
showtabs=false,                 % show tabs within strings adding particular underscores
morekeywords={var},
%  frame=single,                   % adds a frame around the code
tabsize=2,                  % sets default tabsize to 2 spaces
captionpos=none,                   % sets the caption-position to bottom
breaklines=true,                % sets automatic line breaking
breakatwhitespace=false,        % sets if automatic breaks should only happen at whitespace
title=\lstname,                 % show the filename of files included with \lstinputlisting; also try caption instead of title
escapeinside={(*}{*)},          % if you want to add a comment within your code
keywordstyle=\ttfamily\bfseries,
otherkeywords={->,::,rec}
% commentstyle=\color{Gray},
% stringstyle=\color{Green}
}

\input{macro-comments}
\input{macros}
\newcommand{\apx}{\sqsupseteq}
\newcommand\qc{QuickCheck\xspace}
\newcommand\sch{SmallCheck\xspace}
\newcommand\se{\symbolic execution\xspace}
\newcommand\name{our approach\xspace}
\title{Partition Checking}

\author
{DRAFT}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{document}

\maketitle

\begin{abstract}
Property-Based Testing (PBT) is widely used in functional programming
to test programs. Approaches to PBT in functional programming include
well-known libraries such as Quickcheck or Smallcheck. Unfortunately,
for programs that involve invariants or pre-conditions, those PBT
libraries require users to manually write some extra, often
non-trivial, functions in order to provide effective testing. These
functions include test data generators or functions that shrink
counter-examples.

This paper proposes an alternative approach to PBT based on symbolic
execution. In contrast to black-box, library-based approaches such as
Quickcheck or Smallcheck, our testing approach is language-based and
white-box. The white-box nature of the approach means that it can exploit
the definitions of the functions and properties being tested.
This removes the need of manual test data generators, thus
moving the burden of carefully analyzing the program and properties
under test from the programmer to the computer. Moreover, symbolic execution makes it possible to explore execution paths that neither random testing nor bounded-exhaustive approach can easily cover.
Therefore our approach is able to find corner case bugs that QuickCheck and SmallCheck can hardly find.
To prove the effectiveness of our approach in practice we developed a small Mini-ML style
functional language and conducted several case studies to compare
various property-based testing approaches. The results indicate
that finding counter-examples with a symbolic-based testing approach
is competitive and sometimes better than Quickcheck, while avoiding
extra code for generators or shrinking functions.
\end{abstract}

%include sections/Introduction.lhs
%include sections/Review.lhs
%include sections/Overview.lhs
%include sections/Formalization.lhs
%include sections/CaseStudies.lhs
%include sections/RelatedWork.lhs
%include sections/Conclusion.lhs

\bibliographystyle{plain}
\bibliography{literature}

\end{document}
