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
import Data.List ( intersect, nub, sort )
\end{code}

We straight forwardly implement the powersetconstruction . Here, we translate a NFA, $N=(Q,\Sigma , \delta, q_0, F)$, 
where $Q$ is the set of states, $\Sigma$ is the alphabet, $\delta$ is the transition function $\delta : Q\times \Sigma \rightarrow \mathcal{P}(Q)$, $q_0\in Q$ the initial state 
and $F\subseteq Q$ the set of final states. We define the corrsponding DFA as $D=(Q',\Sigma , \delta',q,F')$ where
\begin{itemize}
    \item $Q'=\mathcal{P}(Q)$
    \item $\delta' : Q'\times \Sigma\rightarrow Q', \; \delta'(S,x)=\delta'(\bigcup_{q\in S}\{ \delta(q,x)\} ,\varepsilon )$
    \item $q=\delta(q_0,\varepsilon)$
    \item $F'= Q'\cap F$ 
\end{itemize}
Instead of using sets for the Powerset construction, we will use lists. 
Therefore, we have to take care of sorting the list to not run into problems evolving from \texttt{[0,1]} not being the same as \texttt{[1,0]}. 
While the definition of the alphabet, initial and acceptance states is straightforward, the definition of the transition function is a bit more involved. 
The problems when implementing this mainly arise from having partial functions as transitions. After presenting the \texttt{nfaToDfa} function, we will further elaborate on this.

\begin{code}
powerSetList :: [a] -> [[a]]
powerSetList [] = [[]]
powerSetList (x:xs) = map (x:) (powerSetList xs) ++ powerSetList xs

nfaToDfa :: (Eq state, Ord state) => NFA state symbol -> DFA [state] symbol
nfaToDfa (NFA statesN alphabetN transN startN endN) =
  let nfa = NFA statesN alphabetN transN startN endN
      statesD = map sort $ powerSetList statesN                                          -- new set of states
      alphabetD = alphabetN                                                   -- same alphabet as the NFA
      startD = sort $ epsilonClosure nfa startN                                      -- the set of all states reachable from initial states in the NFA by epsilon-moves
      endD = filter (\state -> not $ null (state `intersect` endN)) statesD   -- All states that contain an endstate.
      transD (st, sy) =                                                       -- 
          Just $ sort $ nub $ concatMap (epsilonClosure nfa) syTransitionsForDfaStates where        -- epsilonClosure of the sy-reachable states
            syTransitionsForDfaStates = concatMap (\s -> transitionNFA nfa (s, Just sy)) st  -- states reachable by sy-transitions
  in  DFA statesD alphabetD transD startD endD

\end{code}
 The function $\texttt{transD}$ takes a state \texttt{sf} in the new DFA  (which is a list of states in the original NFA) and a symbol \texttt{sy} and returns a state in the DFA (also a list).
First, the lambda function \texttt{\\s -> transitionNFA nfa (s, Just sy)} is concatmapped over \texttt{st}. This gives us a list of all states reachable from the states in \texttt{st} by a \texttt{sy}-transition. 
In the next step, we have to add all states reachable by a $\varepsilon$-transition as these are, in the original NFA, reachable without reading a symbol. 
In the original algorithm we would be done here, but as we use lists instead of sets, we have to apply the functions \texttt{nub} and \texttt{sort} to make mirror the behaviour of sets in the sense that two sorted and nubbed lists are equal when they have the same elements in them.

The proof that the resulting DFA accepts exactly the same strings as the original NFA works by induction on the length of the input string and is almost completely represented in the definitions of the translation. 
The base case follows because the initial state in the DFA is the epsilon closure of the original initial staes which are exactly the states reachable given the empty string as input. 
This mirrors the definition of the initial state and endstate. 
The induction step uses that the states one can reach after reading a symbol $x$  is the $\varepsilon$-closure of the set of $x$-reachable states. 
This is mirrored by the two steps in the definition of \texttt{transD}. The complete proof can be found in any text book on automata theory.
See for instance Theorem 1.39 from \cite{sipser2012}.

To minimize the DFA, we first find all the unreachable states and then delete them in the next step. To find all the unreachable states, we start from the initial state and then check whether there is a string
that allows one to reach that state from the initial state. The \texttt{nextStates} function, takes a state and returns all states reachable by any character in the alphabet. We use this \texttt{nextStates} in the 
\texttt{closing} function. This function takes two lists of states as arguments and returns another list of states. The returned list contains all states that can be reached from the second list. 
To not end up in loops, we keep track of all states already visited using a list \texttt{visited}. 

We use the function \texttt{findReachableStates} to define the set of states in the new DFA which are just all states that are reachable from the initial states. 
Then, we restrict the transitions and final states to the reachable states in the original DFA.

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
