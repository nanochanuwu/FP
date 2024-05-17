module DfaAndNfaCode where

data DFA a b = DFA  { statesDFA :: [a]
                    , alphabetDFA :: [b]
                    , transitionDFA :: (a,b) -> a
                    , beginDFA :: a
                    , finalDFA :: [a]
                    }

data NFA a b = NFA  { statesNFA :: [a]
                    , alphabetNFA :: [b]
                    , transitionNFA :: (a,b) -> [a]
                    , beginNFA :: a
                    , finalNFA :: [a]
                    }