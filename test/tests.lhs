\section{Tests}\label{sec:tests}

For our test suite, we use our \texttt{Arbitrary} implementations of DFAs, NFAs and regular expressions
to test whether our conversions preserve the language that the automaton or the regular expression describes.
We also test whether they compose - for instance, whether applying \texttt{regToNfa} and then \texttt{nfaToReg}
to an arbitrary regular expression results in an equivalent regular expression.
We arbitrarily choose \texttt{Int} as our state type and \texttt{Bool} as our symbol type for simplicity,
and because they also both satisfy all constraints that our functions impose on the \texttt{state} and \texttt{symbol} type.

Note that in our test suite, we take for granted that our \texttt{matches} function works, without testing it explicitly.
We think this is reasonable, because the function consists of one of the most basic straightforward direct implementations
of the mathematical definition. We however also tested it manually on small manually generated inputs, which we do not feature here.
Moreover, we make use of the \texttt{simplify} function for regular expressions to speed up the tests.

Finally, it is worth noting that we often had to limit the size of our arbitrarily generated strings
so that our test suite would not take too long to execute. 
These limits were simply set through several test runs.

\begin{code}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import DfaAndNfa ( evaluateDFA, evaluateNFA, NFA, DFA )
import RegExp ( RegExp, matches, simplify )
import RegToNfa (regexToNfa)
import NfaToReg (nfaToReg)
import NfaToDfa (nfaToDfa, removeUnreachableStates)

import Test.Hspec ( hspec, describe )
import Test.Hspec.QuickCheck( prop )
import Test.QuickCheck ( (==>) )

main :: IO ()
main = hspec $ do
  describe "Regular languages: finite automata and regular expressions" $ do
    prop "- simplify regex" $ \(re :: RegExp Bool) s -> length s <= 100 
                                ==> matches s re == matches s (simplify re)
    prop "- regex to nfa" $ \(re :: RegExp Bool) s -> length s <= 100 
                                ==> matches s (simplify re) == evaluateNFA (regexToNfa $ simplify re) s
    prop "- nfa to regex" $ \(nfa :: NFA Int Bool) s -> length s <= 10 
                                ==> evaluateNFA nfa s == matches s (simplify $ nfaToReg nfa)              
    prop "- regex to nfa and back" $ \(re :: RegExp Bool) s -> length s <= 20 
                                ==> matches s (simplify re) == matches s ( (simplify . nfaToReg . regexToNfa ) re )   
    prop "- nfa to regex and back" $ \(nfa :: NFA Int Bool) s -> length s <= 10 
                                ==> evaluateNFA nfa s == evaluateNFA ((regexToNfa . simplify . nfaToReg) nfa) s
    prop "- regex to nfa to dfa" $ \(nfa :: NFA Int Bool) s -> length s <= 10 
                                ==> evaluateNFA nfa s == evaluateNFA ((regexToNfa . simplify . nfaToReg) nfa) s  
    prop "- nfa to dfa" $ \(nfa :: NFA Int Bool) s -> length s <= 25 
                                ==> evaluateNFA nfa s == evaluateDFA (nfaToDfa nfa) s
    prop "- minimize dfa" $ \(dfa :: DFA Int Bool) s -> length s <= 50 
                                ==> evaluateDFA dfa s == evaluateDFA (removeUnreachableStates dfa) s
\end{code}

To run the tests, use \verb|stack test|.

% To also find out which part of your program is actually used for these tests,
% run \verb|stack clean && stack test --coverage|. Then look for ``The coverage
% report for ... is available at ... .html'' and open this file in your browser.
% See also: \url{https://wiki.haskell.org/Haskell_program_coverage}.