\subsection{Converting NFAs to regular expressions: Kleene's Algorithm}\label{subsec:NfaToReg}

\begin{code}
module NfaToReg(nfaToReg) where

import DfaAndNfa ( NFA(NFA) )
import RegExp ( RegExp(..), orAll )
\end{code}


We implement Kleene's Algorithm to convert a given NFA to
an equivalent Regular-Expression.\\
\\
First, given:
\begin{itemize}
\item transition-function \texttt{delta}
\item the alphabet \texttt{labels}
\item A start state \texttt{o}
\item A end state \texttt{d}
\end{itemize}
We compute \texttt{labelsFromTo delta labels o d}, the collection of labels/arrows that take us from \texttt{o} to \texttt{d} in our NFA:


\begin{code}
-- Get collection of labels in a NFA from a given origin state
-- to a destination state.
labelsFromTo :: (Eq state) 
            =>  ((state, Maybe symbol) -> [state])                          -- Transition function
            -> [symbol]                                                     -- Alphabet
            ->  state                                                       -- Origin state
            ->  state                                                       -- Destination state
            ->  [Maybe symbol]                                              -- Collection of labels
labelsFromTo delta labels o d = [label | label <- labels', 
                                         d `elem` delta (o, label)] 
                        where
                         -- labels' = lables \cup {\varepsilon}
                            labels' = fmap Just labels ++ [Nothing]
\end{code}


Then, for a given label (or $\epsilon$-label) we trivially compute the regex for it using \texttt{labelToReg}:


\begin{code}
-- Convert a label (or epsilon)
-- to a Reg-Ex 
labelToReg :: Maybe symbol          -- label read
            -> RegExp symbol        -- Equivalent Reg-Ex
labelToReg Nothing = Epsilon
labelToReg (Just c)  = Literal c 
\end{code}


We then trivially extend this to a list of labels using \texttt{labelsToReg} for example:
\[ \texttt{labelsToReg [a, b, c, $\varepsilon$] $\;=\;$ a | b | c | $\varepsilon$}  \]


\begin{code}
-- Converts a collection of labels
-- to a Reg-Ex
labelsToReg :: [Maybe symbol]       -- Collection of  labels
            -> RegExp symbol        -- Equivalent Reg-Ex
labelsToReg labels = orAll (fmap labelToReg labels) 
\end{code}


Finally, we are now ready to define our helper function \texttt{r} which is the key to our translation.\\
Note however, that \texttt{r} forces two restrictions on our NFA:
\begin{enumerate}
    \item Need \texttt{state == Int} to preform induction on a state

    \item For our list of states, need \texttt{states == [1,2,$\cdots$, n]}
\end{enumerate}
To ensure these restrictions, we define \texttt{correctStates states} to check \texttt{states == [1,2,$\cdots$,n]}:


\begin{code}
-- For our `r` helper function and `nfaToReg`,
-- we need states == [1,2,3, ..., n] for some n >= 0.
-- This predicate checks that states == [1,2,3, ..., n] 
correctStates :: [Int] -> Bool
correctStates states = states == [1..n] where n = length states
\end{code}


Now, for our helper function \texttt{r}:
\begin{adjustwidth}{5em}{}
    for \texttt{i, j $\in$ [1,$\cdots$,n]} and \texttt{k $\in$ [0,1,$\cdots$,n]}:\\ ``\texttt{r k i j}'' means ``All paths in NFA from \texttt{i} to \texttt{j} where all intermediate-states are $\leq \texttt{k}$''\\
    \\
    For example, ``\texttt{r 2 1 3}'' would accept the path
    \[ \texttt{1} \rightarrow \textcolor{blue}{\texttt{2}} \rightarrow \textcolor{blue}{\texttt{1}} \rightarrow \texttt{3} \]
    and reject the path
    \[ \texttt{1} \rightarrow \textcolor{blue}{\texttt{2}} \rightarrow \textcolor{blue}{\texttt{1}} \rightarrow \textcolor{red}{\texttt{3}} \rightarrow \texttt{3} \]   
\end{adjustwidth}

We define this by induction on upperbound \texttt{k} as follows:
\begin{adjustwidth}{5em}{}
    ``Direct labels from \texttt{i} to \texttt{i} OR do nothing''\\
    $\texttt{r$^{\texttt{0}}$ i i \;=\; labelsToReg(labelsFromTo delta labels i i) \;|\; $\epsilon$ }$\\
    \\
    \\
    ``Direct labels from \texttt{i} to \texttt{j}''\\
    $\texttt{r$^{\texttt{0}}$ i j \;=\; labelsToReg(labelsFromTo delta labels i j)}$\\
    \\
    \\
    ``Take a \texttt{k-1}-bounded path that passes through \texttt{k} OR take one that doesn't path through \texttt{k}''\\
    $\texttt{r$^{\texttt{k}}$  i j \;\;=\;\; r$^{\texttt{k-1}}$  i k \;$\cdot$\; (r$^{\texttt{k-1}}$ k k)$^{\texttt{*}}$ \;$\cdot$\; r$^{\texttt{k-1}}$ k j       \;\;\;\;|\;\;\;\;   r$^{\texttt{k-1}}$ i j}$
\end{adjustwidth}
So our code for \texttt{r} is:


\begin{code}
-- Reg-Ex of paths in NFA that go from
-- an origin state to a destination
-- st all intermediate states are <= a given bound k.
r :: ((Int, Maybe symbol) -> [Int])        -- Transition function
    -> [symbol]                            -- Alphabet
    -> Int                                 -- All intermediate-states <= this bound
    -> Int                                 -- Origin state
    -> Int                                 -- Destination state
    -> RegExp symbol                       -- Reg-Ex for all label-paths
          
r delta labels 0 i j   
        | i == j    = labelsToReg (labelsFromTo delta labels i j) `Or` Epsilon
        
        | otherwise = labelsToReg (labelsFromTo delta labels i j)

--  r^{k} ij         = r^{k-1} ik               (r^{k-1} kk)*                   r^{k-1} kj       |               r^{k-1} ij
r delta labels k i j = r' (k-1) i k  `Concat`   Star(r' (k-1) k k)  `Concat`    r' (k-1) k j    `Or`             r' (k-1) i j         
                where r' = r delta labels
\end{code}


Finally, to compute our equivalent regex for \texttt{NFA [1,$\cdots$,n] labels delta start finals}, we define it as:
\[  \bigcup_{\texttt{f1} \,\,\in\,\, \texttt{finals}}\, \texttt{r n start f1}  \]
Thus, our code for \texttt{nfaToReg} is:


\begin{code}
-- Converts an NFA to an equivalent Reg-Exp
-- using kleene's algorithm.
nfaToReg :: NFA Int symbol                                      -- NFA to convert
         -> RegExp symbol                                       -- Equivalent Reg-Ex
nfaToReg (NFA states labels delta start finals) = 
        -- Need states == [1,2,..n] for 
        -- helper function r!
        case correctStates states of
            False -> error "states is not == [1, 2,..., n]"
            
            -- Compute Or_{f1 in finals} r n start f1
            True  -> foldr (\f1 regExp -> r' n start f1  `Or` regExp) Empty finals   
                where r' = r delta labels
                      n  = maximum states
\end{code}