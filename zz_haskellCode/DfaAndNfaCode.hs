module DfaAndNfaCode where

import Data.Function 
import Data.List 
import Data.Maybe


data DFA state symbol = DFA  
                    { statesDFA :: [state]
                    , alphabetDFA :: [symbol]
                    , transitionDFA :: (state,symbol) -> state
                    , beginDFA :: state
                    , finalDFA :: [state]
                    }


data NFA state symbol = NFA  
                    { statesNFA :: [state]
                    , alphabetNFA :: [symbol]
                    , transitionNFA :: (state,symbol) -> [state]
                    , beginNFA :: state
                    , finalFNA :: [state]
                    }

testDFA = DFA [1,2] "ab" (\(st,sy) -> fromJust $ lookup (st,sy) [((1,'a'), 1), ((1,'b'), 2)])  1 [2]
testNFA = NFA [1,2,3] "ab" (\(st,sy) -> fromJust $ lookup (st,sy) [((1,'a'), [1]), ((1,'b'), [1,2]), ((2,'a'), [2]), ((2,'b'), [2])])  1 [2]