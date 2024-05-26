\section{Tests}\label{sec:tests}

\begin{code}
module Main where

import DfaAndNfa ( evaluateDFA, evaluateNFA, NFA )
import RegExp ( RegExp, matches, simplify )
import RegToNfa (regexToNfa)
import NfaToReg (nfaToReg)
import NfaToDfa (nfaToDfa)

import Test.Hspec ( hspec, describe, it )
import Test.QuickCheck ( Testable(property) )

main :: IO ()
main = hspec $ do
  describe "Regular languages: finite automata and regular expressions" $ do
    it "simplify regex" $ property pSimplify
    it "regex to nfa" $ property pRegexToNfa
    -- it "nfa to regex" $ property pNfaToRegex                 -- no Arbitrary NFA yet
    it "regex to nfa and back" $ property pRegexToNfaAndBack    -- note that this might take very long
    -- it "regex to nfa to dfa" $ property pRegexToNfaToDfa     -- fails

pSimplify :: RegExp Bool -> [Bool] -> Bool
pSimplify re s = matches s re == matches s (simplify re)

pRegexToNfa :: RegExp Bool -> [Bool] -> Bool
pRegexToNfa re s = matches s (simplify re) == evaluateNFA (regexToNfa $ simplify re) s

pNfaToRegex :: NFA Int Char -> [Char] -> Bool
pNfaToRegex nfa s = evaluateNFA nfa s == matches s (nfaToReg nfa)

pRegexToNfaAndBack :: RegExp Bool -> [Bool] -> Bool
pRegexToNfaAndBack re s = matches s (simplify re) == matches s ( (simplify . nfaToReg . regexToNfa ) re )

pRegexToNfaToDfa :: RegExp Bool -> [Bool] -> Bool
pRegexToNfaToDfa re s = matches s (simplify re) == evaluateDFA ( ( nfaToDfa . regexToNfa . simplify ) re) s
\end{code}

To run the tests, use \verb|stack test|.

% To also find out which part of your program is actually used for these tests,
% run \verb|stack clean && stack test --coverage|. Then look for ``The coverage
% report for ... is available at ... .html'' and open this file in your browser.
% See also: \url{https://wiki.haskell.org/Haskell_program_coverage}.