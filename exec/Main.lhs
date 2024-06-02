\section{A playground for finite automata and regular expressions} \label{sec:Main}

Here, we manually define a simple DFA and a simple NFA to show some of the most important parts of our code.

\begin{code}
module Main where

import DfaAndNfa ( DFA(DFA), NFA(NFA), printDFA, printNFA )
import NfaToDfa (nfaToDfa, removeUnreachableStates)
import RegExp ( simplify, printRE )
import NfaToReg (nfaToReg)

import Data.Maybe (fromMaybe)
import RegToNfa (regexToNfa)

testDFA :: DFA Int Char -- this accepts the language (a*)(b*)
testDFA = DFA [1,2] 
              "ab" 
              (`lookup` [((1,'a'), 1), ((1,'b'), 2)])
              1
              [2]
                
testNFA :: NFA Int Char -- this accepts all the strings over {a,b}
testNFA = NFA [1,2,3] 
              "ab" 
              (\(st,sy) -> fromMaybe [] $ lookup (st,sy) 
                  [ ((1, Just 'a'), [1]), ((1, Just 'b'), [1,2])
                  , ((1, Nothing), [2]), ((2, Just 'a'), [2])
                  , ((2,Just 'b'), [2]), ((2, Nothing), [3])
                  , ((3, Just 'a'), [2]), ((3, Nothing), [1])]
              )  
              1 
              [2]
\end{code}

It is easy to see that \texttt{testDFA} accepts the language $a^* b^*$,
while \texttt{testNFA} accepts all the strings over the alphabet $\{a,b\}$.

\begin{code}
main :: IO ()
main = do
  putStrLn "\nWelcome to our demo! \n"
  putStrLn "--- test DFA ---"
  putStrLn $ printDFA testDFA
  putStrLn "--- testNFA ---"
  putStrLn $ printNFA testNFA
  putStrLn "--- testNFA to DFA ---"
  putStrLn $ printDFA $ (removeUnreachableStates . nfaToDfa) testNFA
  putStrLn "--- testNFA to regex ---"
  putStrLn $ printRE $ (simplify . nfaToReg) testNFA
  putStrLn "--- testNFA to regex and back ---"                                      -- note that this is quite large already!
  putStrLn $ printNFA $ regexToNfa $ (simplify . nfaToReg) testNFA
  -- putStrLn "--- testNFA to regex and back and to DFA ---"                        -- this might take VERY long
  -- putStrLn $ printDFA $ nfaToDfa $ regexToNfa $ (simplify . nfaToReg) testNFA
\end{code}

We can run this program with the commands \texttt{stack build && stack exec myprogram}.

% The output of the program is something like this:

% \begin{verbatim}
% Hello!
% [1,2,3,4,5,6,7,8,9,10]
% [100,100,300,300,500,500,700,700,900,900]
% [1,3,0,1,1,2,8,0,6,4]
% [100,300,42,100,100,100,700,42,500,300]
% GoodBye!
% \end{verbatim}
