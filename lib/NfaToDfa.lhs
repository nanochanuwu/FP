\section{The Powerset construction} \label{sec:NfaToDfa}

We begin by defining the Powerset for lists. 
This should give us a list of lists containing for each element of the powerset a list that has the same elements. 

\begin{code}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module NfaToDfa where

import DfaAndNfa
    ( DFA(DFA, beginDFA, transitionDFA, finalDFA, alphabetDFA),
      NFA(NFA, transitionNFA),
      epsilonClosure )
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.List ( intersect, nub, sort )

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

powerSetList :: [a] -> [[a]]
powerSetList [] = [[]]
powerSetList (x:xs) = map (x:) (powerSetList xs) ++ powerSetList xs


nfaToDfa :: Ord a => NFA a b -> DFA [a] b
nfaToDfa (NFA statesN alphabetN transN startN endN) =
  let nfa = NFA statesN alphabetN transN startN endN
      statesD = powerSetList statesN
      alphabetD = alphabetN
      -- QUESTION: Why are we taking epsilon-closure here?
      -- Sipser (page 55) doesn't take epsilon-closure
      startD = epsilonClosure nfa startN
      endD = filter (\state -> not $ null (state `intersect` endN)) statesD
      transD (st, sy) =
          -- QUESTION: Why are we taking epsilon-closure here?
          Just $ nub $ concatMap (epsilonClosure nfa) syTransitionsForDfaStates where 
            syTransitionsForDfaStates = concatMap (\s -> transitionNFA nfa (s, Just sy)) st 
  in  DFA statesD alphabetD transD startD endD



-- Use small adjustment of epsilonClosure function to find all reachable states from a given set of initial states
findReachableStatesDFA :: forall state symbol . (Eq state, Ord state) => DFA state symbol -> [state] -> [state]
findReachableStatesDFA dfa initialStates = sort . nub $ closing [] initialStates where
  closing :: Eq state => [state] -> [state] -> [state] 
  closing visited [] = visited
  closing visited (y:ys)
    | y `elem` visited = closing visited ys
    | otherwise = closing (y : visited) (ys ++ nextStates y) 
  nextStates :: state -> [state]
  nextStates state = mapMaybe (\sym -> transitionDFA dfa (state, sym)) (alphabetDFA dfa) -- checks for the next states following "state" 

-- Function to remove unreachable states from a DFA
removeUnreachableStates :: (Eq state, Ord state, Eq symbol) => DFA state symbol -> DFA state symbol
removeUnreachableStates dfa = DFA reachableStates (alphabetDFA dfa) newTransition (beginDFA dfa) newFinalStates where
  reachableStates = findReachableStatesDFA dfa [beginDFA dfa] -- Other states cannot play a role in the evaluation of strings
  transitionsToReachables = [((s, a), transitionDFA dfa (s, a)) | s <- reachableStates, a <- alphabetDFA dfa]
  newTransition (s, a) = fromMaybe (error "Invalid transition") (lookup (s, a) transitionsToReachables)
  newFinalStates = filter (`elem` reachableStates) (finalDFA dfa)

\end{code}
