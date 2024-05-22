\section{DFAs and NFAs} \label{sec:DfaAndNfa}

\begin{code}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module DfaAndNfa where

import Data.List ( sort )
import Data.Maybe ( fromMaybe )

data DFA state symbol = DFA
                    { statesDFA :: [state]
                    , alphabetDFA :: [symbol]
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

{-
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
-}


testDFA :: DFA Integer Char
testDFA = DFA [1,2] "ab" (`lookup` [((1,'a'), 1), ((1,'b'), 2)])  1 [2]
testNFA :: NFA Integer Char
testNFA = NFA [1,2,3] "ab" (\(st,sy) -> fromMaybe [] $ lookup (st,sy) [((1, Just 'a'), [1]), ((1, Just 'b'), [1,2]), ((1, Nothing), [2]), ((2, Just 'a'), [2]), ((2,Just 'b'), [2]), ((2, Nothing), [3]), ((3, Just 'a'), [2]), ((3, Nothing), [1])])  1 [2]


evaluateDFA :: forall state symbol . Eq state => DFA state symbol -> [symbol] -> Bool
evaluateDFA (DFA _ _ delta begin final) syms = case walkDFA (Just begin) syms of
    Nothing -> False
    Just s -> s `elem` final
    where -- ugly helper function to handle the Maybe's
        walkDFA :: Maybe state -> [symbol] -> Maybe state
        walkDFA Nothing _ = Nothing
        walkDFA (Just q) [] = Just q
        walkDFA (Just q) (s:ss) = case delta (q,s) of
            Nothing -> Nothing
            Just q' -> walkDFA (Just q') ss


-- Close the set {x} under epsilon-arrows
epsilonClosure :: (Eq state, Ord state) => NFA state symbol -> state -> [state]
epsilonClosure nfa x = sort $ closing [] [x] where
  closing visited [] = visited
  closing visited (y:ys)
    | y `elem` visited = closing visited ys
    | otherwise = closing (y : visited) (ys ++ transitionNFA nfa (y, Nothing))


-- This is U_{x in xs} epsilonClosure nfa x
epsilonClosureSet :: (Eq state, Ord state) => NFA state symbol -> [state] -> [state]
epsilonClosureSet nfa = concatMap (epsilonClosure nfa)

-- Implementation from here: https://en.wikipedia.org/wiki/Nondeterministic_finite_automaton

evaluateNFA :: forall state symbol . (Eq state, Ord state) => NFA state symbol -> [symbol] -> Bool

                                                                        -- Cannot tell for recursive case if
                                                                        -- "wa" is "a : w" or "w ++ [a]"
                                                                        -- in wikipedia article (assumed it was latter).
evaluateNFA nfa syms = any (`elem` finalNFA nfa) (walkNFA (beginNFA nfa) (reverse syms)) where
    walkNFA :: state -> [symbol] -> [state]
    -- delta*(q, epsilon) = E {q} 
    walkNFA   q  []       = epsilonClosureSet nfa [q]
    
    -- delta*(q, w ++ [a]) = U_{r in delta*(q, w)} E(delta(r,a))
    walkNFA q (a : w)      = concatMap (\r -> epsilonClosureSet nfa (delta (r, Just a))) walkNFA' where
        delta = transitionNFA nfa
        
        -- delta*(q, w)
        walkNFA' = walkNFA q w

\end{code}