\section{DFAs and NFAs} \label{sec:DfaAndNfa}

In this section we will define the data types DFA and NFA.

\subsection{Mathematical Definition and Haskell Implementation}

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

We have implemented these definitions as closely as possible in the data type definitions below. 

\begin{code}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}

module DfaAndNfa where

import Data.Maybe ( fromMaybe, fromJust, isJust )
import Test.QuickCheck( Arbitrary(arbitrary), Gen, elements, frequency, listOf1, sublistOf, suchThat, vectorOf, chooseInt )
import Data.List (nub)

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
\end{code}

There are a couple of things to note about the implementation.
First, the types \texttt{state} and \texttt{symbol} are both arbitrary. That is, we can construct DFAs and NFAs with values of any type (though some functions might not perform as intended, 
given that they have some type constraint, we will mention these whene they come up). 
Second, notice how the $\delta^{DFA}$ function maps a tuple of type \texttt{state} and \texttt{symbol} to the type \texttt{Maybe state}. The reason for 
this is that $\delta^{DFA}$ can be a partial function, potentially leading to exceptions when excecuting functions call the transition function. To handle 
such exceptions more easily we implement $\delta^{DFA}$ to map to \texttt{Maybe state}, returning \texttt{Nothing} whenever the function is not defined for a particular
combination of $(state, symbol)$. We make the necessary steps to and from the \texttt{Maybe} context within the functions requiring such conversions themselves.
Third, $\delta^{NFA}$ maps a tuple of type \texttt{state} and \texttt{Maybe symbol} to the type \texttt{[state]}, where the empty list is returned when the function is not defined for a $(state,$ Maybe $symbol)$ combination. 
We choose to represent $\Sigma \cup \{\varepsilon\}$ using \texttt{Maybe symbol} as it provides the additional value to the alphabet by which we can represent $\varepsilon$-transitions. Here too we make the conversion to and
from \texttt{Maybe} within the functions that require these conversions themselves.

Below we detail the implementation of ancilliary functions and instance declarations for the DFA and NFA data types.

\subsection{Functions for DFAs and NFAs}

\subsubsection*{Evaluate DFA and NFA}
Below we define the function \texttt{evaluateDFA}, implemented from \cite{sipser2012}.

\begin{code}
evaluateDFA :: forall state symbol . Eq state => DFA state symbol -> [symbol] -> Bool
evaluateDFA dfa syms = case walkDFA (Just $ beginDFA dfa) syms of
    Nothing -> False -- If walkDFA returns Nothing at any point, evaluateDFA returns False
    Just s -> s `elem` finalDFA dfa   {- Otherwise, if walkDFA can make a transition for each symbol in the string, 
                                         evaluateDFA checks whether the state it walked to is a sate in the list of final states. -}
    where -- helper function to handle the Maybe's
        walkDFA :: Maybe state -> [symbol] -> Maybe state
        walkDFA Nothing _ = Nothing 
        walkDFA (Just q) [] = Just q
        walkDFA (Just q) (s:ss) = case transitionDFA dfa (q,s) of
            Nothing -> Nothing -- If transitionDFA dfa (q,s) returns Nothing (i.e. it cannot make an s transition from state q), then the walkDFA returns Nothing.
            Just q' -> walkDFA (Just q') ss -- If transitionDFA dfa (q,s) returns Just q', then we continue walkDFA with ss from q'.
\end{code}

The \texttt{evaluateDFA} function takes a specific DFA and checks whether the DFA accepts the list of symbols (of the same type as the symbols in the DFA's alphabet) we give it. 
It does so by walking along the DFA  according to the symbols in the list (by means of the \texttt{walkDFA} helper function) and checks whether the state it ends at is one of the final states of the DFA.
Due to our use of the \texttt{`elem`} function, our \texttt{evaluateDFA} function has an equality constraint on the symbol type.

Next we implement the same function for NFAs, the \texttt{eveluateNFA} function (implemented from \cite{sipser2012}). 
In this function we will have to consider the $\varepsilon$-closure for certain states, so we first define two functions called 
\texttt{epsilonClosure} and \texttt{epsilonClosureSet}. These functions will also figure in the conversion of NFAs to DFAs later on.

\begin{code}
epsilonClosure :: forall state symbol . Eq state => NFA state symbol -> state -> [state]
epsilonClosure nfa x = closing [] [x] where
    closing :: [state] -> [state] -> [state]
    closing visited [] = visited {- visited acts as an accumulator which will be returned as the epsilon closed 
                                    list of states once the function has gone through all the states it needs to close. -} 
    closing visited (y:ys)
        | y `elem` visited = closing visited ys -- If y has already been visited we move on
        | otherwise = closing (y : visited) (ys ++ transitionNFA nfa (y, Nothing))  
        -- otherwise we add y to the visited states and add all its 
        -- epsilon related states to the yet to close list and recur the closing.

epsilonClosureSet :: Eq state => NFA state symbol -> [state] -> [state]
epsilonClosureSet nfa = concatMap (epsilonClosure nfa)

evaluateNFA :: forall state symbol . Eq state => NFA state symbol -> [symbol] -> Bool
evaluateNFA nfa syms = any (`elem` finalNFA nfa) (walkNFA [beginNFA nfa] syms) where
    walkNFA :: [state] -> [symbol] -> [state]
    walkNFA states [] = epsilonClosureSet nfa states -- base case for the empty list of symbols, returns the epsilon-reachable states from the current set of states.
    walkNFA states (s:ss) = walkNFA (concatMap transition epsilonClosureStates) ss where  
        -- recursively takes the epsilon-closure of the current set and finds all the s-reachable states from those 
        -- and feeds it back into the walkNFA function.
        transition q = transitionNFA nfa (q, Just s) -- helper function for readability.
        epsilonClosureStates = epsilonClosureSet nfa states
\end{code}

The \texttt{evaluateNFA} function is quite similar to the \texttt{evaluateDFA} function. There are two notable differences however.

First, because the \texttt{transitionNFA} function does not return \texttt{Maybe state}, but rather \texttt{[state]}, we do not have to distinguish cases. Second, the \texttt{evaluateNFA} function first takes 
the $\varepsilon$-closure of the current set of states before finding all the states that are reachable from each of those states by the corresponding symbol-transition. The \texttt{epsilonClosure} function  
recursively finds all the $\varepsilon$-reachable states from the the initial state we want to close. It does so by finding the $\varepsilon$-reachable states for each element in the yet-to-close list of states and
adding these to the list. It then adds the element to the accumulator list \texttt{visited}, marking the specific state as closed. It then recurs through the yet-to-close list (adding the results to the list and 
the closed element to \texttt{visited} each time, skipping over elements that have already been closed) until it has gone through the entire list, whereupon it returns the \texttt{visited} list. The function 
\texttt{epsilonClosureSet} extends this function to a list of states.

Because we make use of the \texttt{`elem`} function in both \texttt{epsilonClosure} and \texttt{evaluateNFA}, both of these functions also require an instance of \texttt{Eq} to be defined for the state type of the
respective NFA.

Next we define a pretty print function for both DFA and NFA.

\subsubsection*{Pretty Print for DFA and NFA}

The following code implements pretty print functions for both DFAs and NFAs.

\begin{code}
printDFA :: (Show state, Show symbol) => DFA state symbol -> String
printDFA (DFA states alphabet transition begin final) =
    "States: " ++ show states ++ "\n" ++
    "Alphabet: " ++ show alphabet ++ "\n" ++
    "Start State: " ++ show begin ++ "\n" ++
    "Final States: " ++ show final ++ "\n" ++
    "Transitions:\n" ++ unlines (map showTransition allTransitions)
  where
    showTransition ((state, sym), nextState) =
        show state ++ " -- " ++ show sym ++ " --> " ++ show nextState --    q -- s --> q'
    allTransitions = [((state, sym), fromJust $ transition (state, sym)) | state <- states, sym <- alphabet, isJust $ transition (state, sym) ]

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

Each of these functions is essentially the same for both types. They both return a string that shows each part of the DFA/NFA, while nicely representing the transitions we can make from each state.

We will now move on to the \texttt{instance Show} and \texttt{instance Arbitrary} declarations for both the DFA and NFA data types.

\subsection{Instance Declarations DFA and NFA}
In this section we detail the instance Show and instance Arbitrary declarations for DFA and NFA. Both of these instances need to be defined for both the DFA data type and the NFA data type
in order for the quickCheck test-suite to function. 

First we discuss the implementation of \texttt{instance Show}.

\subsubsection*{Instance Show DFA and NFA}
Below you find the code for \texttt{instance Show DFA}

\begin{code}
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
\end{code}
This implementation of instance Show DFA returns (as per convention) a string containing valid Haskell code, given our definition of the DFA data type. It generates a lookup table containing all the
transitions we can make from a given state for a given symbol and prints the function by prepending "\texttt{`lookup`}" to this table, returning \texttt{Just s}, for some state s, whenever it finds an entry in the list
for a specific $(state, symbol)$ combination, and otherwise returning Nothing.

The implementation for \texttt{instance Show NFA} is almost identical to that for DFA. We again return a string containing valid Haskell code given our implementation of the NFA data type.

\begin{code}
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

Here too we generate a lookup table containing all the possible transitions we can make from any given state. We ensure that \texttt{transitionNFA} is a valid Haskell function by prepending 
"\texttt{fromMaybe [] \$ lookup }" to the table. The function will then return \texttt{s} if the \texttt{lookup} function returns \texttt{Just s}, for some state s, and returning the 
empty list (\texttt{[]}) if the lookup function returns Nothing.

\subsubsection*{Instance Arbitrary DFA and NFA}

We now move on to on to our implementation of instance Arbitrary DFA and NFA. These instances are essential to the quickTest test-suite, as they dictate how the arbitrary DFAs and NFAs are generated during the testing procedure.

We begin by taking a closer look at our implementation of \texttt{instance Arbitrary DFA}.

\begin{code}
instance (Arbitrary state, Arbitrary symbol, Eq state, Eq symbol, Num state, Ord state) => Arbitrary (DFA state symbol) where
    arbitrary :: (Arbitrary state, Arbitrary symbol, Eq state, Eq symbol) => Gen (DFA state symbol)
    arbitrary = do
            states <- listOf1 (arbitrary :: Gen state) -- generates a nonempty list of arbitrary states
            alphabet <- uniqueAlphabet -- generates a list of length 2 of unique arbitrary symbols
            transition <- randomTransitionDFA states alphabet -- generates the arbitrary transition function with the appropriate type
            begin <- elements states -- takes an random element in the list of states to be the begin state
            final <- sublistOf states `suchThat` (not . null) -- takes a nonempty sublist of the states to be designated final states
            return $ DFA (nub states) alphabet transition begin final 
        where 
            -- helper function to generate the list of unique arbitrary sybols, always has length 2
            uniqueAlphabet = do
                x <- (arbitrary :: Gen symbol)
                y <- (arbitrary :: Gen symbol) `suchThat` (/= x)
                return [x, y]
            -- helper function to generate the transition function of arbitrary DFA
            randomTransitionDFA states alphabet = do
                st <- (nub <$> listOf1 (elements states)) `suchThat` (not . null) -- generates a non-empty list consisting of elements of the list of states
                syms <- vectorOf (length st) (elements alphabet) -- generates a vector of the length of st consisting of the (possibly duplicate) elements of the alphabet
                st' <- listOf1 (elements states) -- generates a non-empty list consisting of (possibly duplicate) elements of the list of states
                let transitionTable = zip (zip st syms) st' -- creates the transistion table
                return $ \(state, symbol) -> lookup (state, symbol) transitionTable 
\end{code}

For each of the arguments of the DFA constructor we define how to arbitraryly generate the right value. 
For the states we generate a non-empty list of the state type of the DFA. For the alphabet we generate a list of length 2 of unique values.

\begin{code}
instance (Arbitrary symbol, Eq symbol) => Arbitrary (NFA Int symbol) where
    arbitrary :: (Arbitrary symbol, Eq symbol) => Gen (NFA Int symbol)
    arbitrary = do
            n <- chooseInt (2,5) -- generates a random element n in the range (2,5).
            let states = [1..n] -- sets the states to the list of 1 to n.
            alphabet <- uniqueAlphabet -- generates a list of length 2 of unique arbitrary symbols
            transition <- randomTransitionNFA states alphabet -- generates the arbitrary transition function with the appropriate type
            begin <- elements states -- takes an random element in the list of states to be the begin state
            final <- sublistOf states `suchThat` (not . null) -- takes a nonempty sublist of the states to be designated final states
            return $ NFA (nub states) alphabet transition begin final
        where 
            uniqueAlphabet = do
                x <- (arbitrary :: Gen symbol)
                y <- (arbitrary :: Gen symbol) `suchThat` (/= x)
                return [x, y]
            -- helper function to generate the transition function of arbitrary NFA
            randomTransitionNFA states alphabet = do
                st <- (nub <$> listOf1 (elements states)) `suchThat` (not . null)  -- generates a non-empty list consisting of unique elements of the list of states
                syms <- vectorOf (length st) $ frequency [(1, return Nothing), (20, elements (map Just alphabet))] -- generates a vector of the length of st where the elements are either Nothing or a Just element in the alphabet
                stList <- listOf1 $ sublistOf states -- generates a non-empty list consisting of subsets of the list of states
                let transitionTable = zip (zip st syms) stList -- creates the transistion table
                return $  \(state, symbol) -> fromMaybe [] $ lookup (state, symbol) transitionTable
\end{code}
