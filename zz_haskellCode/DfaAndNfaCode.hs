module NFA_AND_DFA where

data DFA a b =  { statesDFA :: [a]
                , alphabetDFA :: [b]
                , transitionDFA :: (a,b) -> a
                , beginDFA :: a
                , finalDFA :: a
                }

data NFA a b =  { statesNFA :: [a]
                , alphabetNFA :: [b]
                , transitionNFA :: (a,b) -> [a]
                , beginNFA :: a
                , finalFNA :: a
                }

