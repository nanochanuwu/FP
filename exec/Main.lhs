\section{A playground for finite automata and regular expressions} \label{sec:Main}

\begin{code}
module Main where

main :: IO ()
main = do
  putStrLn "Hello!"
\end{code}

% We can run this program with the commands:

% \begin{verbatim}
% stack build
% stack exec myprogram
% \end{verbatim}

% The output of the program is something like this:

% \begin{verbatim}
% Hello!
% [1,2,3,4,5,6,7,8,9,10]
% [100,100,300,300,500,500,700,700,900,900]
% [1,3,0,1,1,2,8,0,6,4]
% [100,300,42,100,100,100,700,42,500,300]
% GoodBye!
% \end{verbatim}
