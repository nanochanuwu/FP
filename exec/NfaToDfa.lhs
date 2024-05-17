\section{The Powerset construction}

We begin by defining the Powerset for lists. 
This should give us a list of lists containing for each element of the powerset a list that has the same elements. 

\begin{code}
powersetList :: [a] -> [[a]]
powersetList [] = []
powersetList x:xs = map (x:) powersetList xs ++ powersetList xs
\end{code}
