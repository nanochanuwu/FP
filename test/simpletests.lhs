\section{Simple Tests}
\label{sec:simpletests}

We now use the library QuickCheck to randomly generate input for our functions
and test some properties.

\begin{code}
module Main where

import RegExp ( RegExp, matches, simplify )
import RegToNfa ( regexToNfa )
import DfaAndNfa ( evaluateDFA, evaluateNFA, NFA )

import Test.Hspec ( hspec, describe, it )
import Test.QuickCheck ( Testable(property) )
import NfaToReg (nfaToReg)
import NfaToDfa (nfaToDfa)

main :: IO ()
main = hspec $ do
  describe "Basics" $ do
    it "simplify regex" $ property pSimplify
    it "regex to nfa" $ property pRegexToNfa
    -- it "nfa to regex" $ property pNfaToRegex
    it "regex to nfa and back" $ property pRegexToNfaAndBack
    it "regex to nfa to dfa" $ property pRegexToNfaToDfa

pSimplify :: RegExp Bool -> [Bool] -> Bool
pSimplify re s = matches s re == matches s (simplify re)

pRegexToNfa :: RegExp Bool -> [Bool] -> Bool
pRegexToNfa re s = matches s re == evaluateNFA (regexToNfa re) s

pNfaToRegex :: NFA Int Char -> [Char] -> Bool
pNfaToRegex nfa s = evaluateNFA nfa s == matches s (nfaToReg nfa)

pRegexToNfaAndBack :: RegExp Bool -> [Bool] -> Bool
pRegexToNfaAndBack re s = matches s re == matches s ( (simplify . nfaToReg . regexToNfa ) re )

pRegexToNfaToDfa :: RegExp Bool -> [Bool] -> Bool
pRegexToNfaToDfa re s = matches s re == evaluateDFA ( nfaToDfa $ regexToNfa re) s
\end{code}

To run the tests, use \verb|stack test|.

To also find out which part of your program is actually used for these tests,
run \verb|stack clean && stack test --coverage|. Then look for ``The coverage
report for ... is available at ... .html'' and open this file in your browser.
See also: \url{https://wiki.haskell.org/Haskell_program_coverage}.