\section{Converting Reg back to NFA } \label{sec:RegToNfa}

\begin{code}
module RegToNfa where

import RegExp ( RegExp(..) )
import DfaAndNfa ( NFA(NFA) )
import Data.List ( union )
import Data.Maybe ( isNothing )

regexToNfa :: Eq sym => RegExp sym -> NFA Int sym
regexToNfa re = fst $ regexToNfaHelper re 1 where
    -- auxiliary function used to build an NFA equivalent to the given regex
    -- its second parameter is the first available int to name the NFA's states
    -- returns the NFA built from the smaller regex's, and the next first available int
    regexToNfaHelper :: Eq sym => RegExp sym -> Int -> (NFA Int sym, Int)
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
            | st `elem` f1 && isNothing sy = [b2] -- epsilon-transitions from old NFA1's final states to NFA2's start state
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
            -- ERROR: Disagrees with Sisper (page 63) here:
            -- Should probably be:
            -- "st `elem` f && isNothing sy = [b] `union` d(st, Nothing)"
            | st `elem` f && isNothing sy = [b] -- epsilon-transitions from final states to old start state
            | otherwise = d (st,sy)
        begin = n'
        final = [n'] `union` f
        next = n'+1
\end{code}