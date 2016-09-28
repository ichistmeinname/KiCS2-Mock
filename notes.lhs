\documentclass{scrreprt}

\usepackage[backend=bibtex]{biblatex}

\usepackage{hyperref}

%include lhs2Tex.fmt
\begin{document}

\section*{The Idea}
Do not store decisions if the associated value is not shared.

\section*{The Approach}
\begin{itemize}
\item use static analysis to decide where no values are shared
\item use uniqueness types as a stronger kind of "static analysis"; non-deterministic code generated for values of unique types can be optimised with regard to decision tracking (e.g., no ID for choices)
\end{itemize}

\paragraph{The Problem}

All data types are translated by adding a special constructor for non-deterministic values prefixed |Choice_|. %
Going towards the first idea, we would also like to add a choice constructor without IDs. %

\begin{spec}
data C_Int = C_Int Int
           | Choice_C_Int ID C_Int C_Int
           | ChoiceNoID_C_Int C_Int C_Int
\end{spec}

Now consider the following example. %

\begin{spec}
dup x = x + x

id x = x
coin = 1 ? 2

example1 = dup (id coin)
example2 = id coin
\end{spec}

The function |coin| non-deterministically computes the values |1| and |2|, but does not introduce any sharing as well as the function |id|. %
The more interessting function here is |dup| that uses its argument |x| two times, thus, introduces sharing, and its application in the function |example|. %

In a simplified version of the current translation scheme, the following Haskell code is generated -- the only interessting part here is the non-deterministic function |coin|. %

\begin{spec}
dup x = x + x

id x = x
coin supply = Choice_C_Int (thisID supply) (C_Int 1) (C_Int 2)

example1 supply = dup (id (coin supply))
example2 supply = id (coin supply)
\end{spec}

Every non-deterministic function gets an additional argument: a supply of IDs, which are used in choice constructors. %
Because |example1| and |example2| use a non-determinstic function, they need an ID supply as well, which they feed to |coin|. %
In our approach we would like to use choices without IDs whenever possible in order to reduce memory costs. %
The first problem that arises is that we do not want to traverse the code in the end againg to finally decide that we do not need the IDs afterall. %

\paragraph{Solution 1}

So the first idea is to actually generate two versions of every non-deterministic function and use information of the callee in order to decide which version to use. %

\begin{spec}
dup :: C_Int -> C_Int
dup x = x + x

id :: a* -> a
id x = x

nd_coin :: IDSupply* -> C_Int
nd_coin supply = Choice_C_Int (thisID supply) (C_Int 1) (C_Int 2)

nd_wos_coin :: C_Int
nd_wos_coin = ChoiceNoID_C_Int (C_Int 1) (C_Int 2)

example1 :: IDSupply* -> C_Int
example1 supply = dup (id (nd_coin supply))

example2 :: C_Int
example2 supply = id nd_wos_coin
\end{spec}

In this example the types tagged with |*|s are Uniqueness Types, signalising that argument in question is used only once (or not at all). %

The downside of this approach is that our code size suffers as we generate each non-determinstic function twice. %
However, the same kind of code duplication is tolerated when defining higher-order functions: since we cannot annotate that the higher-order argument is guaranteed to be non-determinstic -- or deterministic, two versions of the function are generated and in concrete applications the applicable version is chosen. %

\paragraph{Solution 2}

Instead of generating two versions, we can propagate the information based on the Uniqueness Types one step earlier in order to inline "harmless" non-determinstic functions. %

\begin{spec}
dup :: C_Int -> C_Int
dup x = x + x

id :: a* -> a
id x = x

coin :: IDSupply* -> C_Int
coin supply = Choice_C_Int (thisID supply) (C_Int 1) (C_Int 2)

example1 :: IDSupply* -> C_Int
example1 supply = dup (id (nd_coin supply))

example2 :: C_Int
example2 supply = id (ChoiceNoID_C_Int (C_Int 1) (C_Int 2))
\end{spec}

\end{document}
