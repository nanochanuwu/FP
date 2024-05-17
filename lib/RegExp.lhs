\section{Regular Expressions}\label{sec:reg_exp}

% definition of regular expression
% \begin{definition}
    Fix an alphabet $\Sigma$. Say that $R$ is \emph{regular expression} over $\Sigma$ if:
    \begin{enumerate}[(i)]
        \item $R=a$ for some $a\in\Sigma$;
        \item $R=\varnothing$,
        \item $R=\varepsilon$,
        \item $R=R_1 \cup R_2$, where $R_1,R_2$ are regular expressions,
        \item $R=R_1 \cdot R_2$, where $R_1,R_2$ are regular expressions,
        \item $R=(R_1)^*$, where $R_1$ is a regular expression.
    \end{enumerate}
% \end{definition}

\begin{code}

module RegExp where

data RegExp sym = Empty
                | Epsilon
                | Literal sym
                | Or (RegExp sym) (RegExp sym)
                | Concat (RegExp sym) (RegExp sym)
                | Star (RegExp sym)

oneOrMore :: RegExp sym -> RegExp sym -- abbreviation for +
oneOrMore re = re `Concat` Star re

orAll :: [RegExp sym] -> RegExp sym
orAll = foldr Or Empty

concatAll :: [RegExp sym] -> RegExp sym 
concatAll = foldr Concat Empty

prettyPrint :: Show sym => RegExp sym -> String
prettyPrint Empty = "\2205" -- unicode for \varnothing
prettyPrint Epsilon = "\0949" -- unicode for \varepsilon
prettyPrint (Literal x) = show x
prettyPrint (re1 `Or` re2) = prettyPrint re1 ++ "|" ++ prettyPrint re2
prettyPrint (re1 `Concat` re2) = prettyPrint re1 ++ prettyPrint re2
prettyPrint (Star re) = "(" ++ prettyPrint re ++ ")*"

\end{code}

% algebra of regular expressions

\begin{code}

-- todo: simplify regexp
-- might be useful for the translations regexp from/to automata?

\end{code}