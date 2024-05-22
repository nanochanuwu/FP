\section{Kleene's Algorithm} \label{sec:NfaToReg}

We implement Kleene's Algorithm to convert a given Nfa to
an equivalent Regular-Expression.

\begin{code}

module NfaToReg where

import DfaAndNfa
import RegExp

-- Convert a label (or epsilon)
-- to a Reg-Ex 
labelToReg :: Maybe symbol          -- label read
            -> RegExp symbol        -- Equivalent Reg-Ex
labelToReg Nothing = Epsilon
labelToReg (Just c)  = Literal c 


-- COnverts a collection of labels
-- to a Reg-Ex in the obvious way, ie:
    -- labelsToReg ['a', 'b', 'c', ε]  = 'a' | 'b' | 'c' | 'ε' 
labelsToReg :: [Maybe symbol]       -- Collection of  labels ∪ ε
            -> RegExp symbol        -- Equivalent Reg-Ex
labelsToReg labels = foldr Or Empty (fmap labelToReg labels)


-- Reg-Ex of paths in NFA that go from
-- an origin state to a destination
-- without going through states >= a given state.
r :: (Eq state, Num state)
    =>  ((state, Maybe symbol) -> [state])                       -- Transition function
    -> [symbol]                                                  -- Alphabet
    -> state                                                     -- Cannot go-through states >= this one
    -> state                                                     -- Origin state
    -> state                                                     -- Destination state
    -> RegExp symbol                                             -- Reg-Ex for all label-paths

-- R^{0} ij          =  a_{1} | ... | a_{m}         q_{j} in  Δ(q_{i}, a_{1}) ∪ ... ∪ Δ(q_{i}, a_{m})
r delta labels 0 i j = labelsToReg (labelsFromTo delta labels i j)

--  R^{k} ij         = R^{k-1} ik               (R^{k-1} kk)*                   R^{k-1} kj       |               R^{k-1} ij
r delta labels k i j = r' (k-1) i k  `Concat`   Star(r' (k-1) k k)  `Concat`    r' (k-1) k j    `Or`             r' (k-1) i j         
                 where r' = r delta labels



-- Converts an NFA to an equivalent Reg-Exp
-- using kleene's algorithm.

-- NOTE: MAY NOT have right behvaiour for
-- state != Int
nfaToReg :: (Num state, Ord state)
         => NFA state symbol                                      -- NFA to convert
         -> RegExp symbol                                       -- Equivalent Reg-Ex
nfaToReg (NFA states labels delta start finals) = foldr (\f1 regExp -> r' n start f1  `Or` regExp) Empty finals   
                where r' = r delta labels
                      n  = maximum states
 






\end{code}
