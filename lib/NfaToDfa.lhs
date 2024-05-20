\section{The Powerset construction}

We begin by defining the Powerset for lists. 
This should give us a list of lists containing for each element of the powerset a list that has the same elements. 

\begin{code}

module NfaToDfa where

import DfaAndNfa
import Data.Maybe ( fromMaybe )
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
    allTransitions = [((state, sym), transition (state, sym)) | state <- states, sym <- alphabet]

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
    allTransitions = [((state, sym), transition (state, sym)) | state <- states, sym <- Nothing : map Just alphabet]

powerSetList :: [a] -> [[a]]
powerSetList [] = [[]]
powerSetList (x:xs) = map (x:) (powerSetList xs) ++ powerSetList xs


nfaToDfa :: Ord a => NFA a b -> DFA [a] b
nfaToDfa (NFA statesN alphabetN transN startN endN) =
  let nfa = NFA statesN alphabetN transN startN endN
      statesD = powerSetList statesN
      alphabetD = alphabetN
      startD = epsilonClosure nfa startN
      endD = filter (\state -> not $ null (state `intersect` endN)) statesD
      transD (st, sy) =
          nub $ concatMap (epsilonClosure nfa) syTransitionsForDfaStates where 
            syTransitionsForDfaStates = concatMap (\s -> transitionNFA nfa (s, Just sy)) st 
  in  DFA statesD alphabetD transD startD endD



-- Use small adjustment of epsilonClosure function to find all reachable states from a given set of initial states
findReachableStatesDFA :: (Eq state, Ord state) => DFA state symbol -> [state] -> [state]
findReachableStatesDFA dfa initialStates = sort . nub $ closing [] initialStates where
  closing visited [] = visited
  closing visited (y:ys)
    | y `elem` visited = closing visited ys
    | otherwise = closing (y : visited) (ys ++ nextStates y) 
  nextStates state = map (\sym -> transitionDFA dfa (state, sym)) (alphabetDFA dfa) --checks for the next states following "state" 

-- Function to remove unreachable states from a DFA
removeUnreachableStates :: (Eq state, Ord state, Eq symbol) => DFA state symbol -> DFA state symbol
removeUnreachableStates dfa = DFA reachableStates (alphabetDFA dfa) newTransition (beginDFA dfa) newFinalStates where
  reachableStates = findReachableStatesDFA dfa [beginDFA dfa] -- Other states cannot play a role in the evaluation of strings
  transitionsToReachables = [((s, a), transitionDFA dfa (s, a)) | s <- reachableStates, a <- alphabetDFA dfa]
  newTransition (s, a) = fromMaybe (error "Invalid transition") (lookup (s, a) transitionsToReachables)
  newFinalStates = filter (`elem` reachableStates) (finalDFA dfa)

\end{code}
