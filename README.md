# KiCS2-Mock

This is a very reduced version of the [KiCS2])http://www-ps.informatik.uni-kiel.de/kics2) runtime environment. KiCS2 is a compiler for the functional logic programming language Curry.
In additional to the runtime environment, this repository includes a small Prelude that defines native Curry datatypes (`C_Bool`, `List_OP`s and `C_ValueSequence`s) and a small module with some tests.

# Motivation
After modelling some problems ([puzzles])https://github.com/ichistmeinname/Puzzles) and [probabilistic programming](https://github.com/ichistmeinname/ProbabilisticProgramming)) by means of Curry's built-in nondeterminsm, I stumpled upon a space leak when using [SetFunctions][]. SetFunctions are used to collect all possible values of a nondeterminstic expression. That is, in my applications I used SetFunctions, because I am interested in all solutions of my defined problem: all solutions for a given puzzle, the probability for all occuring events.
With these multiple applications of SetFunctions in mind, I found it quite disappointing that such an important function is a problem for KiCS2. Thus, I started investigationg the root of this memory leak.

# Running example

I started my investigation with a very simple example.


    foldLists = foldr (&&) True (foldr1 (:) (replicate veryLargeNumber True))
    foldValues = foldValues (&&) True (foldr1 (?) (replicate veryLargeNumber True))

    veryLargeNumber = 1000000000
    -- (?) :: a -> a -> a -- nondetermistic choice between two values


Folding all values of a nondeterministic expression is basically the same as folding a list. Or isn't it? Unfortunately, folding all values of a nondeterministic expression causes this space leak; and guess what: it was the main functionalty that I used in my applications to process nondeterministic values (e.g., counting all solutions).


![foldr memory usage](/images/foldr.ps)
![foldValues memory usage](/images/foldValues.ps)


As a side note: the unnecesary `foldr`-usage in order to build a list is suppose to mimic the nondeterminstic version, where I produce a nondeterminstic choice for every element of the (very large) list.


# Tracing the runtime environment (aka why I build this mock-up)

# First results

[setfunctions]: https://www.informatik.uni-kiel.de/~mh/papers/PPDP09.pdf