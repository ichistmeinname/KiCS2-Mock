# KiCS2-Mock

This is a very reduced version of the [KiCS2](http://www-ps.informatik.uni-kiel.de/kics2) runtime environment. KiCS2 is a compiler for the functional logic programming language Curry.
In additional to the runtime environment, this repository includes a small Prelude that defines native Curry datatypes (`C_Bool`, `List_OP`s and `C_ValueSequence`s) and a small module with some tests.

# Motivation
After modelling some problems ([puzzles](https://github.com/ichistmeinname/Puzzles) and [probabilistic programming](https://github.com/ichistmeinname/ProbabilisticProgramming)) by means of Curry's built-in nondeterminsm, I stumpled upon a space leak when using [SetFunctions][1]. SetFunctions are used to collect all possible values of a nondeterminstic expression. That is, in my applications I used SetFunctions, because I am interested in all solutions of my defined problem: all solutions for a given puzzle, the probability for all occuring events.
With these multiple applications of SetFunctions in mind, I found it quite disappointing that such an important function is a problem for KiCS2. Thus, I started investigationg the root of this memory leak.

## Running example

I started my investigation with a very simple example.


    foldLists = foldr (&&) True (foldr1 (:) (replicate veryLargeNumber True))
    foldValues = foldValues (&&) True (set2 foldr1 (?) (replicate veryLargeNumber True))

    veryLargeNumber = 1000000000
    -- (?) :: a -> a -> a -- nondetermistic choice between two values


Folding all values of a nondeterministic expression is basically the same as folding a list. Or isn't it? Unfortunately, folding all values of a nondeterministic expression causes this space leak; and guess what: it was the main functionalty that I used in my applications to process nondeterministic values (e.g., counting all solutions).


![foldr memory usage](/images/foldr.pdf)
![foldValues memory usage](/images/foldValues.pdf)


As a side note: the unnecesary `foldr`-usage in the defintion `foldLists` order to build a list is suppose to mimic the nondeterminstic version, where I produce a nondeterminstic choice for every element of the (very large) list.


## Tracing the runtime environment (aka why I build this mock-up)

# First results

Nondeterministic expressions are simply reduced to a `SearchTree`.

    data SearchTree a = Value a
                      | Or ID (SearchTree a) (SearchTree a)
    type ID = Integer
                      
That is, every expression `x ? y` will produce a corresponding SearchTree `Or 1 (Value x) (Value y)` during runtime, e.g., `foldr1 (?) [True, True, True]` becomes `Or 1 (Value True) (Or 3 (Value True) (Or 5 (Value True) (Value True)))`. As we go along this SearchTree in order to evaluate an expression, the path we take down the SearchTree has to be stored because of Curry's call-time choice semantic. Therefore, each node within the Search is labeled with an unique identifier, and if we pass such a node in order to take the left (or right) subtree, our decision for this node will be mapped to `Left` (or `Right`). In the following, we call the storage for this value pairs `decision-map`.

    data Decision = NoDecision
                  | ChooseLeft
                  | ChooseRight

We need to access the decision-map that stores all these value pairs at any time during evaluation, because for any shared nondeterminstic value, we need to make the same decision for every occurrence of that value in the given expression.

    > let x = True ? False in [x,x]
    [True,True]
    [False,False]

That is, as we feed the decision-map more and more values, it takes more and more space in memory. In case that we encouter a shared value , we cannot throw away any decisions that we've made so far.


## Testing environment

    main = genBool 100000 >>= print . fold'


Profiling:

   Fri May 29 18:05 2015 Time and Allocation Profiling Report  (Final)

   testMock +RTS -p -s -h -RTS

   total time  =        0.55 secs   (549 ticks @ 1000 us, 1 processor)  
   total alloc = 932,623,408 bytes  (excludes profiling overheads)

|COST CENTRE | MODULE | %time | %alloc |
|------------|--------|-------|--------|
|getDecisionRaw               | Mock        | 21.3  | 11.1 |
|searchMSearch'.decide        | Mock        | 14.8  | 12.7 |
|onDecisionMap                | Mock        | 13.7  | 11.9 |
|setDecisionGetChange.unchain | Mock        |  5.1  |  6.7 |
|setDecisionGetChange         | Mock        |  4.9  |  8.7 |
|nextSupplies.nextNSupplies'  | Mock        |  4.0  |  6.2 |
|setDecision                  | Mock        |  3.5  |  7.9 |
|lookupDecisionID             | Mock        |  3.1  |  3.1 |
|searchMSearch'               | Mock        |  2.7  |  6.9 |
|>>=                          | MockPrelude |  2.4  |  1.4 |
|genBool                      | Main        |  2.2  |  2.2 |
|searchMSearch'.mChoice       | Mock        |  2.2  |  2.7 |
|setDecisionRaw               | Mock        |  2.0  |  2.9 |
|lookupDecision               | Mock        |  2.0  |  2.2 |
|match                        | MockPrelude |  1.8  |  1.4 |
|$!!                          | MockPrelude |  1.3  |  0.0 |
|d_apply                      | MockPrelude |  1.3  |  0.3 |
|searchMSearch'.mChoice.follow| Mock        |  1.3  |  2.8 |
|genBool.ids                  | Main        |  1.1  |  0.9 |
|getUnique                    | Mock        |  1.1  |  0.0 |
|nfChoice                     | Mock        |  0.5  |  1.6 |
|lookupDecisionID.follow      | Mock        |  0.2  |  1.0 |


[1]: https://www.informatik.uni-kiel.de/~mh/papers/PPDP09.pdf  
