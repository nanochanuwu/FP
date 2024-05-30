\section{DFAs and NFAs} \label{sec:DfaAndNfa}
\begin{definition}
    We define a deterministic finite automaton (DFA) as a 5-tuple $\langle Q , \Sigma, \delta, q_0, F \rangle$ where
    \begin{enumerate}[(i)]
        \item Q is a finite set of states,
        \item $\Sigma$ is a finite set of symbols (the alphabet),
        \item $\delta^{DFA} : Q \times \Sigma \to Q $ is a transition function,
        \item $q_0 \in Q$ is the start state,
        \item $F \subseteq Q$ is a set of final states.
    \end{enumerate}
\end{definition}

\begin{definition}
    We define a nondeterministic finite automaton (NFA) as a 5-tuple $\langle Q , \Sigma, \delta, q_0, F \rangle$ where
    \begin{enumerate}[(i)]
        \item Q is a finite set of states,
        \item $\Sigma$ is a finite set of symbols (the alphabet),
        \item $\delta^{NFA} : Q \times \Sigma \cup \{\varepsilon\} \to \mathcal{P}(Q)$ is a transition function,
        \item $q_0 \in Q$ is the start state,
        \item $F \subseteq Q$ is a set of final states.
    \end{enumerate}
\end{definition}

We have implemented these definitions as closely as possible in the data type definitions below. There are a couple of things to note about this. 
First, notice how the $\delta^{DFA}$ function maps a tuple of type \texttt{state} and \texttt{symbol} to the type \texttt{Maybe state}. The reason for 
this is that $\delta^{DFA}$ can be a partial function, potentially leading to exceptions when excecuting functions call the transition function. To handle 
such exceptions more easily we implement $\delta^{DFA}$ to map to \texttt{Maybe state}, returning \texttt{Nothing} whenever the function is not defined for a particular
combination of $(st, sy)$. We make the necessary steps to and from the \texttt{Maybe} context within the functions requiring such conversions themselves.
Second, $\delta^{NFA}$ maps a tuple of type \texttt{state} and \texttt{Maybe symbol} to the type \texttt{[state]}. We choose to represent $\Sigma \cup \{\varepsilon\}$ using 
\texttt{Maybe symbol} as it provides the additional value to the alphabet by which we can represent $\varepsilon$-transitions. Here too we make the conversion to and
from \texttt{Maybe} within the functions that require these conversions themselves.

\begin{code}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
module DfaAndNfa where

import Test.QuickCheck
    ( Arbitrary(arbitrary),
      elements,
      frequency,
      listOf1,
      sublistOf,
      suchThat,
      vectorOf,
      Gen )
import Data.Maybe ( fromMaybe )

--------------------------- data type DFA and NFA definition
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

-- Dummy DFA for testing purposes
testDFA :: DFA Integer Char
testDFA = DFA   [1,2] 
                "ab" 
                (`lookup` [((1,'a'), 1), ((1,'b'), 2)])
                1
                [2]
                
-- Dummy NFA for testing purposes
testNFA :: NFA Integer Char
testNFA = NFA   [1,2,3] 
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
Documentation here

\begin{code}
--------------------------- Instance declarations for NFA and DFA

-- Arbitrary instance for DFA. This is necessary for implementing the autotests.
instance (Arbitrary state, Arbitrary symbol, Eq state, Eq symbol) => Arbitrary (DFA state symbol) where
    arbitrary :: (Arbitrary state, Arbitrary symbol, Eq state, Eq symbol) => Gen (DFA state symbol)
    arbitrary = do
            states <- listOf1 Test.QuickCheck.arbitrary -- generates a nonempty list of arbitrary states
            alphabet <- vectorOf 2 Test.QuickCheck.arbitrary -- generates a vector of length 2 of arbitrary symbols
            transition <- randomTransitionDFA states alphabet -- generates the arbitrary transition function with the appropriate type
            begin <- elements states -- takes an random element in the list of states to be the begin state
            final <- sublistOf states `suchThat` (not . null) -- takes a nonempty sublist of the states to be designated final states
            return $ DFA states alphabet transition begin final -- injects the arbitrary DFA into the Gen mondad
        where 
            -- helper function to generate the transition function of arbitrary DFA
            randomTransitionDFA states alphabet = do
                st <- listOf1  (elements states) -- generates a non-empty list consisting of (possibly duplicate) elements of the list of states
                syms <- vectorOf (length st) (elements alphabet) -- generates a vector of the length of st consisting of the (possibly duplicate) elements of the alphabet
                st' <- listOf1 (elements states) -- generates a non-empty list consisting of (possibly duplicate) elements of the list of states
                let transitionTable = zip (zip st syms) st' -- creates the transistion table
                return $ \(state, symbol) -> lookup (state, symbol) transitionTable -- injects the arbitrary transition function into the Gen monad

-- Arbitrary instance for NFA. This is necessary for implementing the autotests.
instance (Arbitrary state, Arbitrary symbol, Eq state, Eq symbol, Num symbol) => Arbitrary (NFA state symbol) where
    arbitrary :: (Arbitrary state, Arbitrary symbol, Eq state, Eq symbol, Num symbol) => Gen (NFA state symbol)
    arbitrary = do
            states <- listOf1 arbitrary -- generates a nonempty list of arbitrary states
            alphabet <- vectorOf 2 Test.QuickCheck.arbitrary -- generates a vector of length 2 of arbitrary symbols
            transition <- randomTransitionNFA states alphabet -- generates the arbitrary transition function with the appropriate type
            begin <- elements states -- takes an random element in the list of states to be the begin state
            final <- sublistOf states `suchThat` (not . null) -- takes a nonempty sublist of the states to be designated final states
            return $ NFA states alphabet transition begin final -- injects the arbitrary DFA into the Gen mondad
        where 
            randomTransitionNFA states alphabet = do
                st <- listOf1  (elements states) -- generates a non-empty list consisting of (possibly duplicate) elements of the list of states
                syms <- vectorOf (length st) $ frequency [(1, return Nothing), (3, elements (map Just alphabet))] -- generates a vector of the length of st where the elements are either Nothing or a Just element in the alphabet
                stList <- listOf1 $ sublistOf states -- generates a non-empty list consisting of subsets of the list of states
                let transitionTable = zip (zip st syms) stList -- creates the transistion table
                return $  \(state, symbol) -> fromMaybe [] $ lookup (state, symbol) transitionTable -- injects the arbitrary transition function into the Gen monad


-- Show instance for DFA
instance (Show state, Show symbol) => Show (DFA state symbol) where
    show :: (Show state, Show symbol) => DFA state symbol -> String
    show dfa = "DFA {" ++
               "  statesDFA = " ++ show (statesDFA dfa) ++ 
               "  alphabetDFA = " ++ show (alphabetDFA dfa) ++ 
               "  transitionDFA = `lookup` " ++ show transitionListDFA ++ 
               "  beginDFA = " ++ show (beginDFA dfa) ++ 
               "  finalDFA = " ++ show (finalDFA dfa) ++ 
               "  }" 
                where 
                    -- Generates lookup table
                    transitionListDFA :: [((state,symbol), Maybe state)]
                    transitionListDFA = [((st, sy), transitionDFA dfa (st, sy)) 
                                        | st <- statesDFA dfa, 
                                        sy <- alphabetDFA dfa]

-- Show instance for NFA
instance (Show state, Show symbol) => Show (NFA state symbol) where
    show :: (Show state, Show symbol) => NFA state symbol -> String
    show nfa = "NFA {"++
               "  statesNFA = " ++ show (statesNFA nfa) ++ 
               "  alphabetNFA = " ++ show (alphabetNFA nfa) ++ 
               "  transitionNFA = fromMaybe [] $ lookup " ++ show transitionListNFA ++
               "  beginNFA = " ++ show (beginNFA nfa) ++ 
               "  finalNFA = " ++ show (finalNFA nfa) ++
               "  }"
               where
                    -- Generates lookup table
                    transitionListNFA :: [((state, Maybe symbol), [state])]
                    transitionListNFA = [((st, sy), transitionNFA nfa (st, sy)) 
                                        | st <- statesNFA nfa, 
                                          sy <- Nothing : map Just (alphabetNFA nfa)]

\end{code}
Documentation here

\begin{code}
--------------------------- Functions for NFA and DFA

-- evaluate function for DFA. Checks whether a given string of symbols results in a final state. 
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
epsilonClosure :: forall state symbol . Eq state => NFA state symbol -> state -> [state]
epsilonClosure nfa x = closing [] [x] where
    closing visited [] = visited -- visited acts as an accumulator which will be returned as the epsilon closed list of states once the function has gone through all the states it needs to close. 
    closing visited (y:ys)
        | y `elem` visited = closing visited ys -- If y has already been visited we move on
        | otherwise = closing (y : visited) (ys ++ transitionNFA nfa (y, Nothing)) -- otherwise we add y to the visited states and add all its epsilon related states to the yet to close list and recur the closing.

-- This is U_{x in xs} epsilonClosure nfa x
epsilonClosureSet :: Eq state => NFA state symbol -> [state] -> [state]
epsilonClosureSet nfa = concatMap (epsilonClosure nfa)

-- Implementation from here: https://en.wikipedia.org/wiki/Nondeterministic_finite_automaton
evaluateNFA :: forall state symbol . Eq state => NFA state symbol -> [symbol] -> Bool
evaluateNFA nfa syms = any (`elem` finalNFA nfa) (walkNFA (beginNFA nfa) (reverse syms)) where
    walkNFA :: state -> [symbol] -> [state]
    -- delta*(q, epsilon) = E {q} 
    walkNFA   q  []       = epsilonClosureSet nfa [q]
    -- delta*(q, w ++ [a]) = U_{r in delta*(q, w)} E(delta(r,a))
    walkNFA q (a : w)      = concatMap (\r -> epsilonClosureSet nfa (delta (r, Just a))) walkNFA' where
        delta = transitionNFA nfa
        -- delta*(q, w)
        walkNFA' = walkNFA q w

-- Secondary evaluate function for NFAs. There is some error in one of the two, but we have yet to find out which.
evaluateNFA' :: forall state symbol . Eq state => NFA state symbol -> [symbol] -> Bool
evaluateNFA' nfa syms = any (`elem` finalNFA nfa) (walkNFA [beginNFA nfa] syms) where
    walkNFA :: [state] -> [symbol] -> [state]
    walkNFA states [] = epsilonClosureSet nfa states
    walkNFA states (s:ss) = walkNFA (concatMap transition epsilonClosureStates) ss where
        transition q = transitionNFA nfa (q, Just s)
        epsilonClosureStates = epsilonClosureSet nfa states


-- Pretty print function for DFA
printDFA :: (Show state, Show symbol) => DFA state symbol -> String
printDFA (DFA states alphabet transition begin final) =
    "States: " ++ show states ++ "\n" ++
    "Alphabet: " ++ show alphabet ++ "\n" ++
    "Start State: " ++ show begin ++ "\n" ++
    "Final States: " ++ show final ++ "\n" ++
    "Transitions:\n" ++ unlines (map showTransition allTransitions)
  where
    showTransition ((state, sym), nextState) =
        show state ++ " -- " ++ show sym ++ " --> " ++ show nextState
    allTransitions = [((state, sym), transition (state, sym)) | state <- states, sym <- alphabet ]

-- Pretty print function for DFA
printNFA :: (Show state, Show symbol) => NFA state symbol -> String
printNFA (NFA states alphabet transition begin final) =
    "States: " ++ show states ++ "\n" ++
    "Alphabet: " ++ show alphabet ++ "\n" ++
    "Start State: " ++ show begin ++ "\n" ++
    "Final States: " ++ show final ++ "\n" ++
    "Transitions: \n" ++ unlines (map showTransition allTransitions)
  where
    showTransition ((state, Nothing), nextStates) =
        show state ++ " -- " ++ "eps" ++ " --> " ++ show nextStates
    showTransition ((state, Just sym), nextStates) =
        show state ++ " -- " ++ show sym ++ " --> " ++ show nextStates
    allTransitions = [((state, sym), transition (state, sym)) | state <- states, sym <- Nothing : map Just alphabet, not $ null $ transition (state,sym)]
    
\end{code}
