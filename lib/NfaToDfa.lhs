\subsection{The Powerset construction}\label{subsec:NfaToDfa}

In this section, we implement the Powerset construction. 
The powerset construction is an algorithm that transforms a NFA into a equivalent DFA where equivalent means that they accept exactly the same strings.

\begin{code}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module NfaToDfa where

import DfaAndNfa
    ( DFA(DFA, beginDFA, transitionDFA, finalDFA, alphabetDFA),
      NFA(NFA, transitionNFA),
      epsilonClosure )
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.List ( intersect, nub )
\end{code}

\begin{code}
-- Move to DfaAndNfa
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

-- takes a list and returns a list of all sublists. These "powerlist" will take the role of the powerset in the original powerset construction.
\end{code}

We straight forwardly implement the powersetconstruction . Here, we translate a NFA, $N=(Q,\Sigma , T, q_0, F)$, 
where $Q$ is the set of states, $\Sigma$ is the alphabet, $T$ is the transitions function $T:Q\times \Sigma )\rightarrow Q$, $q_0\in Q$ the initial state 
and $F\subseteq Q$ the set of final states. We define the corrsponding DFA as $D=(Q',\Sigma , T',q,F') where
\begin{itemize}
    \item $Q'=\mathcal{P}(Q)$
    \item T':Q'\times \Sigma\rightarrow Q', T'((S,x))=T'(\bigcup_{q\in S}\{ T(q,x)\} ,\epsilon )$
    \item $q=T(q_0,\epsilon )
    \item $F'= Q'\cap F$ 
\end{itemize}

\begin{code}

powerSetList :: [a] -> [[a]]
powerSetList [] = [[]]
powerSetList (x:xs) = map (x:) (powerSetList xs) ++ powerSetList xs

nfaToDfa :: Eq state => NFA state symbol -> DFA [state] symbol
nfaToDfa (NFA statesN alphabetN transN startN endN) =
  let nfa = NFA statesN alphabetN transN startN endN
      statesD = powerSetList statesN                                          -- new set of states
      alphabetD = alphabetN                                                   -- same alphabet as the NFA
      startD = epsilonClosure nfa startN                                      -- the set of all states reachable from initial states in the NFA by ε-moves
      endD = filter (\state -> not $ null (state `intersect` endN)) statesD   -- All states that "contain" an endstate.
      transD (st, sy) =                                                       -- 
          Just $ nub $ concatMap (epsilonClosure nfa) syTransitionsForDfaStates where        -- epsilonClosure of the "sy"-reachable states
            syTransitionsForDfaStates = concatMap (\s -> transitionNFA nfa (s, Just sy)) st  -- states reachable by "sy"-transitions
  in  DFA statesD alphabetD transD startD endD

\end{code}

To minimize the DFA, we first find all the unreachable states and then delete them in the next step. To find all the unreachable states, we start from the initial state and then check whether there is a string
that allows one to reach that state from the initial state. To not end up in loops, we keep track of all states visited using a list "visited". 

\begin{code}
findReachableStatesDFA :: forall state symbol . Eq state => DFA state symbol -> [state] -> [state]
findReachableStatesDFA dfa initialStates = nub $ closing [] initialStates where
  closing :: Eq state => [state] -> [state] -> [state] 
  closing visited [] = visited
  closing visited (y:ys)
    | y `elem` visited = closing visited ys
    | otherwise = closing (y : visited) (ys ++ nextStates y) 
  nextStates :: state -> [state]
  nextStates state = mapMaybe (\sym -> transitionDFA dfa (state, sym)) (alphabetDFA dfa) -- checks for the next states following "state" for any symbol

-- Function to remove unreachable states from a DFA

removeUnreachableStates :: (Eq state, Eq symbol) => DFA state symbol -> DFA state symbol
removeUnreachableStates dfa = DFA reachableStates (alphabetDFA dfa) newTransition (beginDFA dfa) newFinalStates where
  reachableStates = findReachableStatesDFA dfa [beginDFA dfa] -- Other states cannot play a role in the evaluation of strings
  transitionsToReachables = [((s, a), transitionDFA dfa (s, a)) | s <- reachableStates, a <- alphabetDFA dfa]
  newTransition (s, a) = fromMaybe (error "Invalid transition") (lookup (s, a) transitionsToReachables)
  newFinalStates = filter (`elem` reachableStates) (finalDFA dfa)

\end{code}
