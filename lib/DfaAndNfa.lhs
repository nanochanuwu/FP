{-# LANGUAGE InstanceSigs #-}
\section{DFAs and NFAs} \label{sec:DfaAndNfa}

\begin{code}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module DfaAndNfa where

import Test.QuickCheck
import Data.List ( sort, union )
import Data.Maybe ( fromMaybe )

data DFA state symbol = DFA
                    { statesDFA :: [state]
                    , alphabetDFA :: [symbol]
                                                        -- Nothing : state is our "garbage" state.
                                                        -- Reject all strings the moment they reach Nothing : state.
                    , transitionDFA :: (state,symbol) -> Maybe state
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
    show :: (Show state, Show symbol) => DFA state symbol -> String
    show dfa = "DFA {\n" ++
               "  statesDFA = " ++ show (statesDFA dfa) ++ ",\n" ++
               "  alphabetDFA = " ++ show (alphabetDFA dfa) ++ ",\n" ++
               "  transitionDFA = fromJust . flip lookup " ++ show (transitionListDFA dfa) ++ ",\n" ++
               "  beginDFA = " ++ show (beginDFA dfa) ++ ",\n" ++
               "  finalDFA = " ++ show (finalDFA dfa) ++ "\n" ++ 
               "}" 
                where 
                    transitionListDFA :: DFA state symbol -> [((state,symbol),state)]
                    transitionListDFA = undefined

-- Show instance for NFA
instance (Show state, Show symbol) => Show (NFA state symbol) where
    show :: (Show state, Show symbol) => NFA state symbol -> String
    show nfa = "NFA {"++
               "  statesNFA = " ++ show (statesNFA nfa) ++ ",\n" ++
               "  alphabetNFA = " ++ show (alphabetNFA nfa) ++ ",\n" ++
               "  transitionNFA = fromMaybe [] $ lookup " ++ show (transitionListNFA nfa) ++
               "  beginNFA = " ++ show (beginNFA nfa) ++ 
               "  finalFNA = " ++ show (finalNFA nfa) ++
               "}"
               where
                    transitionListNFA :: NFA state symbol -> [((state,symbol), [state])]
                    transitionListNFA = undefined


testDFA :: DFA Integer Char
testDFA = DFA [1,2] "ab" (`lookup` [((1,'a'), 1), ((1,'b'), 2)])  1 [2]
testNFA :: NFA Integer Char
testNFA = NFA [1,2,3] "ab" (\(st,sy) -> fromMaybe [] $ lookup (st,sy) [((1, Just 'a'), [1]), ((1, Just 'b'), [1,2]), ((1, Nothing), [2]), ((2, Just 'a'), [2]), ((2,Just 'b'), [2]), ((2, Nothing), [3]), ((3, Just 'a'), [2]), ((3, Nothing), [1])])  1 [2]

--evaluateDFA :: Eq a => DFA a b -> [b] -> Bool
--evaluateDFA dfa sys = walkDFA (Just $ beginDFA dfa) sys `elem` finalDFA dfa where
--    walkDFA state [] = fromJust state
--    walkDFA state (s:ss) = walkDFA (transitionDFA dfa (state, s)) ss

evaluateDFA :: forall state symbol . Eq state => DFA state symbol -> [symbol] -> Bool
evaluateDFA (DFA _ _ delta begin final) syms = case next of
    Nothing -> False
    Just s -> s `elem` final
    where next = walkDFA (Just begin) syms where
            -- ugly helper function
            walkDFA :: Maybe state -> [symbol] -> Maybe state
            walkDFA Nothing _ = Nothing
            walkDFA (Just q) [] = Just q
            walkDFA (Just q) (s:ss) = case delta (q, s) of
                Nothing -> Nothing
                Just q' -> walkDFA (Just q') ss


evaluateNFA :: Eq a => NFA a b -> [b] -> Bool
evaluateNFA nfa sys =  any (\s -> s `elem` finalNFA nfa) (walkNFA [beginNFA nfa] sys ) where
    delta = transitionNFA nfa
    walkNFA states []     = transition' delta Nothing states
    walkNFA states (c:cs) = walkNFA (transition' delta (Just c) states) cs 


-- Apply Non-determ transition function (including epsilons) to a collection of states:
transition' :: Eq state 
                => ((state, Maybe symbol) -> [state])                       -- Transition function 
                -> Maybe symbol                                             -- Symbol (or epsilon) to read
                -> [state]                                                  -- Current states
                -> [state]                                                  -- Reached states
transition' _ _ []                    = []
transition' delta mc (state : states) = delta (state, Nothing)  `union`   delta (state, mc)   `union`    transition' delta mc states 


epsilonClosure :: (Eq state, Ord state) => NFA state symbol -> state -> [state]
epsilonClosure nfa x = sort $ closing [] [x] where
  closing visited [] = visited
  closing visited (y:ys)
    | y `elem` visited = closing visited ys
    | otherwise = closing (y : visited) (ys ++ transitionNFA nfa (y, Nothing))

\end{code}