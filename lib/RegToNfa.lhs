\subsection{Converting regular expressions to NFAs}\label{subsec:RegToNfa}

Here, we state and implement the construction of the proof of the following lemma. 
Since the implementation is very straightforward, we first prove the lemma
and then briefly discuss a few notable implementation details.

\begin{lemma}
    If a language is described by a regular expression, then it is regular.
\end{lemma}
\begin{proof}
    Fix an arbitrary alphabet $\Sigma$ and let $R$ be a regular expression over $\Sigma$. 
    The proof is by induction on the structure of $R$.
    The basic idea is to construct the simplest possible NFAs for the base cases of $R$, 
    and then make clever transformations to the NFAs given by the inductive hypothesis for the inductive cases.
    We give the full details only of some cases for brevity.

    Case $R=\varnothing$. Then $L(R)=\varnothing$ is accepted by the NFA % states - alphabet - transition - begin - final
    $( \{q_0\} , \Sigma , \delta , q_0 , \varnothing )$ where $\delta(q,s)=\varnothing$ for every $q\in Q$ and $s\in\Sigma$.

    Case $R=\varepsilon$. Then $L(R)=\{\varepsilon\}$ is accepted by the NFA
    $( \{q_0\} , \Sigma , \delta , q_0 , \{q_0\} )$ where $\delta(q,s)=\varnothing$ for every $q\in Q$ and $s\in\Sigma$.

    Case $R=\ell\in\Sigma$. Then $L(R)=\{\ell\}$ is accepted by the NFA
    $( \{q_0,q_1\}, \Sigma, \delta, q_0, \{q_1\} )$ where $\delta(q_0,\ell)=\{q_1\}$ and $\delta(q,s)=\varnothing$ otherwise.

    Case $R=R_1 \cdot R_2$. By the inductive hypothesis, there are NFAs $N_1$ and $N_2$ accepting $L(R_1)$ and $L(R_2)$ respectively.
    We can construct an NFA $N$ that accepts $L(R)$ by adding epsilon-transitions from $N_1$'s final states to $N_2$'s start state,
    \enquote{guessing} where to break the input so that $N_1$ accepts its first substring and $N_2$ its second.
    Formally, let $N_1=(Q_1,\Sigma,\delta_1,q_1,F_1)$ and $N_2=(Q_2,\Sigma,\delta_2,q_2,F_2)$. 
    Then we can define $N=(Q,\Sigma,\delta,q_1,F_2)$, where $Q=Q_1 \cup Q_2$, and \[
        \delta(q,s) = \begin{cases}
            \delta_1(q,s) \text{ if } q \in Q_1\setminus F_1; \\
            \delta_1(q,s) \text{ if } q \in F_1 \text{ and } s\neq\varepsilon; \\
            \delta_1(q,s) \cup \{q_2\} \text{ if } q \in F_1 \text{ and } s=\varepsilon; \\
            \delta_2(q,s) \text{ if } q \in Q_2.
        \end{cases}
    \]
    It is then clear that $L(N)=L(R_1 \cdot R_2)$.

    Case $R=R_1 \cup R_2$. The idea is to glue the NFAs $N_1$ and $N_2$ given by the induction hypothesis to a new start state
    which has epsilon-transitions to the start states of $N_1$ and $N_2$,
    so as to \enquote{guess} whether the input string is in $L(R_1)$ or $L(R_2)$. 

    Case $R=R_1^*$. We build a new NFA $N$ by adding a new start and final state to the NFA $N_1$ given by the induction hypothesis,
    with an epsilon-transition from this state to $N_1$'s start state. 
    This is to guarantee that $N$ accepts $\varepsilon$.
    Moreover, we add epsilon-transitions from $N_1$'s final states to $N_1$'s start state. 
    This is to simulate the fact that $*$ stands for \enquote{arbitrary number of repetitions of the pattern}.
\end{proof}

The implementation of the construction described in the proof is very straightforward, with only a couple technical details.
First, since we do not have a way to know which specific alphabet a regular expression is defined over,
we have to manually define or augment the alphabets in each case. 
The definition of the new transition functions slightly changes accordingly.
Moreover, we need a way to keep track of which labels have been used for the NFA's states.
An easy way to do this is generating an NFA whose states are labelled as \texttt{Int}.
To keep track of the last used \texttt{Int}, we use an auxiliary function \texttt{regexToNfaHelper} to actually construct the NFAs.
The function takes an \texttt{Int} parameter representing the first available integer to label the states,
and return an \texttt{NFA,Int} pair which includes the next available integer.
In short, \texttt{regexToNfaHelper} does all the work, 
and the outer \texttt{regexToNfa} function simply returns the so-constructed NFA discarding the \texttt{Int} output.

\begin{code}
module RegToNfa where

import RegExp ( RegExp(..) )
import DfaAndNfa ( NFA(NFA) )
import Data.List ( union )
import Data.Maybe ( isNothing )

regexToNfa :: Eq symbol => RegExp symbol -> NFA Int symbol
regexToNfa re = fst $ regexToNfaHelper re 1 where
    -- auxiliary function used to build an NFA equivalent to the given regex
    -- its second parameter is the first available int to name the NFA's states
    -- returns the NFA built from the smaller regex's, and the next first available int
    regexToNfaHelper :: Eq symbol => RegExp symbol -> Int -> (NFA Int symbol, Int)
    regexToNfaHelper Empty n = ( NFA [n] [] delta n [], n+1 ) where delta (_,_) = []
    regexToNfaHelper Epsilon n = ( NFA [n] [] delta n [n], n+1 ) where delta (_,_) = []
    regexToNfaHelper (Literal l) n = ( NFA [n,n+1] [l] delta n [n+1], n+2 ) where 
        delta (st,sy) 
            | st == n && sy == Just l = [n+1]
            | otherwise = []
    regexToNfaHelper (Or re1 re2) n = ( NFA states alphabet delta begin final , next ) where
        ( NFA s1 a1 d1 b1 f1, n1 ) = regexToNfaHelper re1 n
        ( NFA s2 a2 d2 b2 f2, n2 ) = regexToNfaHelper re2 n1
        states = s1 `union` s2 `union` [n2] 
        alphabet = a1 `union` a2
        delta (st,sy)
            | st == n2 && isNothing sy = [b1] `union` [b2] -- epsilon-transitions from new start state to old start states
            | st == n2 = []
            | st `elem` s1 = d1 (st,sy)
            | st `elem` s2 = d2 (st,sy)
            | otherwise = []
        begin = n2
        final = f1 `union` f2
        next = n2+1
    regexToNfaHelper (Concat re1 re2) n = ( NFA states alphabet delta begin final , next ) where
        ( NFA s1 a1 d1 b1 f1, n1 ) = regexToNfaHelper re1 n
        ( NFA s2 a2 d2 b2 f2, n2 ) = regexToNfaHelper re2 n1
        states = s1 `union` s2
        alphabet = a1 `union` a2
        delta (st,sy)
            | st `elem` f1 && isNothing sy = [b2] `union` d1 (st,sy) -- epsilon-transitions from old NFA1's final states to NFA2's start state
            | st `elem` s1 = d1 (st,sy)
            | st `elem` s2 = d2 (st,sy)
            | otherwise = []
        begin = b1
        final = f2
        next = n2
    regexToNfaHelper (Star re1) n = ( NFA states alphabet delta begin final , next ) where
        (NFA s a d b f, n' ) = regexToNfaHelper re1 n
        states = s `union` [n']
        alphabet = a
        delta (st,sy)
            | st == n' && isNothing sy = [b] -- epsilon-transitions from new start to old start state
            | st == n' = []
            | st `elem` f && isNothing sy = [b] `union` d (st, Nothing) -- epsilon-transitions from final states also go back to old start state
            | otherwise = d (st,sy)
        begin = n'
        final = [n'] `union` f
        next = n'+1
\end{code}