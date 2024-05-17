\section{DFAs and NFAs}\label{sec:dfa_nfa}

\begin{code}

module DfaAndNfa where

import Data.Function
import Data.List
import Data.Maybe
import Control.Monad



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
                    , finalNFA :: [state]
                    }

-- Show instance for DFA
instance (Show state, Show symbol) => Show (DFA state symbol) where
    show dfa = "DFA {\n" ++
               "  statesDFA = " ++ show (statesDFA dfa) ++ ",\n" ++
               "  alphabetDFA = " ++ show (alphabetDFA dfa) ++ ",\n" ++
               "  transitionDFA = <function>,\n" ++
               "  beginDFA = " ++ show (beginDFA dfa) ++ ",\n" ++
               "  finalDFA = " ++ show (finalDFA dfa) ++ "\n" ++
               "}"

-- Show instance for NFA
instance (Show state, Show symbol) => Show (NFA state symbol) where
    show nfa = "NFA {\n" ++
               "  statesNFA = " ++ show (statesNFA nfa) ++ ",\n" ++
               "  alphabetNFA = " ++ show (alphabetNFA nfa) ++ ",\n" ++
               "  transitionNFA = <function>,\n" ++
               "  beginNFA = " ++ show (beginNFA nfa) ++ ",\n" ++
               "  finalFNA = " ++ show (finalNFA nfa) ++ "\n" ++
               "}"


testDFA :: DFA Integer Char
testDFA = DFA [1,2] "ab" (\(st,sy) -> fromJust $ lookup (st,sy) [((1,'a'), 1), ((1,'b'), 2)])  1 [2]
testNFA :: NFA Integer Char
testNFA = NFA [1,2,3] "ab" (\(st,sy) -> fromMaybe [] $ lookup (st,sy) [((1, Just 'a'), [1]), ((1, Just 'b'), [1,2]), ((1, Nothing), [2]), ((2, Just 'a'), [2]), ((2,Just 'b'), [2]), ((2, Nothing), [3]), ((3, Just 'a'), [2]), ((3, Nothing), [1])])  1 [2]

evaluateDFA :: Eq a => DFA a b -> [b] -> Bool
evaluateDFA dfa sys = walkDFA (beginDFA dfa) sys `elem` finalDFA dfa where
    walkDFA state [] = state
    walkDFA state (s:ss) = walkDFA (transitionDFA dfa (state, s)) ss


evaluateNFA :: Eq a => NFA a b -> [b] -> Bool
evaluateNFA nfa sys =  any (\s -> s `elem` finalNFA nfa) (walkNFA [beginNFA nfa] sys ) where
    delta = transitionNFA nfa
    walkNFA states []     = transition' delta Nothing states
    walkNFA states (c:cs) = walkNFA (transition' delta (Just c) states) cs 


-- Apply Non-determ transition function (including epsilons) to a colletion of states:
transition' :: Eq state 
                => ((state, Maybe symbol) -> [state])                       -- Transition function 
                -> Maybe symbol                                             -- Symbol (or epsilon) to read
                -> [state]                                                  -- Current states
                -> [state]                                                  -- Reached states
transition' _ _ []                    = []
transition' delta mc (state : states) = delta (state, Nothing)  `union`   delta (state, mc)   `union`    transition' delta mc states 



epsilonClosure :: (Eq a, Ord a) => NFA a b -> a -> [a]
epsilonClosure nfa x = sort $ closing [] [x] where
  closing visited [] = visited
  closing visited (y:ys)
    | y `elem` visited = closing visited ys
    | otherwise = closing (y : visited) (ys ++ transitionNFA nfa (y, Nothing))
\end{code}