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
                    , transitionNFA :: (state, Maybe symbol) -> [state]
                    , beginNFA :: state
                    , finalFNA :: [state]
                    }


testDFA = DFA [1,2] "ab" (\(st,sy) -> fromJust $ lookup (st,sy) [((1,'a'), 1), ((1,'b'), 2)])  1 [2]
testNFA = NFA [1,2,3] "ab" (\(st,sy) -> fromJust $ lookup (st,sy) [((1, Just 'a'), [1]), ((1, Just 'b'), [1,2]), ((1, Nothing), [3]), ((2, Just 'a'), [2]), ((2,Just 'b'), [2]), ((3, Just 'a'), [2])])  1 [2]

evaluateDFA :: Eq a => DFA a b -> [b] -> Bool
evaluateDFA dfa sys = walkDFA (beginDFA dfa) sys `elem` finalDFA dfa where
    walkDFA state [] = state
    walkDFA state (s:ss) = walkDFA (transitionDFA dfa (state, s)) ss

{-
evaluateNFA :: Eq a => DFA a b -> [b] -> Bool
evaluateNFA nfa sys = walkDFA (beginDFA nfa) sys `elem` finalDFA nfa where
    walkDFA state [] = state
    walkDFA state (s:ss) = walkDFA (transitionDFA nfa (state, s)) ss
-}