\section{Tests}\label{sec:tests}

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
    prop "- simplify regex" $ \(re :: RegExp Bool) s -> length s <= 100 ==> matches s re == matches s (simplify re)
    prop "- regex to nfa" $ \(re :: RegExp Bool) s -> length s <= 100 ==> matches s (simplify re) == evaluateNFA (regexToNfa $ simplify re) s
    prop "- nfa to regex" $ \(nfa :: NFA Int Bool) s -> length s <= 10 ==> evaluateNFA nfa s == matches s (simplify $ nfaToReg nfa)              
    prop "- regex to nfa and back" $ \(re :: RegExp Bool) s -> length s <= 20 ==> matches s (simplify re) == matches s ( (simplify . nfaToReg . regexToNfa ) re )   
    prop "- nfa to regex and back" $ \(nfa :: NFA Int Bool) s -> length s <= 10 ==> evaluateNFA nfa s == evaluateNFA ((regexToNfa . simplify . nfaToReg) nfa) s
    prop "- regex to nfa to dfa" $ \(nfa :: NFA Int Bool) s -> length s <= 10 ==> evaluateNFA nfa s == evaluateNFA ((regexToNfa . simplify . nfaToReg) nfa) s  
    prop "- nfa to dfa" $ \(nfa :: NFA Int Bool) s -> length s <= 25 ==> evaluateNFA nfa s == evaluateDFA (nfaToDfa nfa) s
    prop "- minimize dfa" $ \(dfa :: DFA Int Bool) s -> length s <= 50 ==> evaluateDFA dfa s == evaluateDFA (removeUnreachableStates dfa) s
\end{code}

To run the tests, use \verb|stack test|.

% To also find out which part of your program is actually used for these tests,
% run \verb|stack clean && stack test --coverage|. Then look for ``The coverage
% report for ... is available at ... .html'' and open this file in your browser.
% See also: \url{https://wiki.haskell.org/Haskell_program_coverage}.