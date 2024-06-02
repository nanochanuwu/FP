\section{Regular Expressions} \label{sec:RegExp}

In this section, we implement the data type for regular expressions, 
as well as some useful functions for matching and simplyfing,
and define an \texttt{Arbitrary} instance for our data type to generate random regular expressions for our test suite.

\begin{definition}
    Fix an alphabet $\Sigma$. We say that $R$ is \emph{regular expression} over $\Sigma$ if:
    \begin{enumerate}[(i)]
        \item $R=a$ for some $a\in\Sigma$;
        \item $R=\varnothing$,
        \item $R=\varepsilon$,
        \item $R=R_1 \cup R_2$, where $R_1,R_2$ are regular expressions,
        \item $R=R_1 \cdot R_2$, where $R_1,R_2$ are regular expressions,
        \item $R=R_1^*$, where $R_1$ is a regular expression.
    \end{enumerate}
\end{definition}

It is also often useful to use the abbreviation $R^+ := R \cup R^*$. 

The following data type definition implements the \texttt{RegExp} type by closely following its formal definition.
Together with the binary union (\texttt{Or}) and concatenation (\texttt{Concat}) operators, we also define their $n$-ary versions for convenience, as well as the \texttt{oneOrMore} abbreviation for $+$.
Finally, we implement a function \texttt{printRE} for displaying regular expressions in a more readable format\footnote{
    This technically operates under the assumption that the alphabet does not contain \texttt{*} or \texttt{+} or the parentheses symbolbols,
    which would make the \texttt{printRE} output ambiguous. Since the only purpose of this function is to display regular expressions in a readable format,
    however, we choose to simply ignore the issue.}.

\begin{code}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}

module RegExp where

import Test.QuickCheck ( Arbitrary(arbitrary), Gen, oneof, sized )

data RegExp symbol = Empty
                | Epsilon
                | Literal symbol
                | Or (RegExp symbol) (RegExp symbol)
                | Concat (RegExp symbol) (RegExp symbol)
                | Star (RegExp symbol)
                deriving (Eq,Show)

oneOrMore :: RegExp symbol -> RegExp symbol
oneOrMore re = re `Concat` Star re

orAll :: [RegExp symbol] -> RegExp symbol
orAll = foldr Or Empty

concatAll :: [RegExp symbol] -> RegExp symbol 
concatAll = foldr Concat Epsilon

printRE :: Show symbol => RegExp symbol -> String
printRE re = case re of
    Empty -> "\2205"                                            -- unicode for \varnothing
    Epsilon -> "\0949"                                          -- unicode for \varepsilon
    Literal l -> show l
    Or re1 re2 -> "(" ++ printRE re1 ++ "|" ++ printRE re2 ++ ")"
    Concat re1 re2 -> printRE re1 ++ printRE re2
    Star re1 -> "(" ++ printRE re1 ++ ")*"
\end{code}

Formally, the language described by a regular expression $R$ over $\Sigma$ is denoted $L(R)$ 
and consists exactly of the strings over $\Sigma$ that match $R$:
intuitively, these are the strings that match the pattern specified by $R$,
where all operators are interpreted in the obvious way, and the $*$ stands for
\enquote{arbitrary number of repetitions of the pattern}.

\begin{definition}
    Let $R$ be a regular expression and $s$ a string, over the same alphabet $\Sigma$. We say that $s$ matches $R$ if:
    \begin{enumerate}[(i)]
        \item if $R=\varnothing$, then never;
        \item if $R=\varepsilon$ and $s=\varepsilon$;
        \item if $R=a\in\Sigma$ and $s=a$;
        \item if $R=R_1 \cup R_2$, and $s$ matches $R_1$ or $s$ matches $R_2$;
        \item if $R=R_1 \cdot R_2$, and there exist $s_1,s_2$ such that $s=s_1s_2$ and $s_1$ matches $R_1$ and $s_2$ matches $R_2$;
        \item if $R=R_1^*$, and $s=\varepsilon$ or $s$ can be split into $n\in\mathbb{N}$ substrings $s_1,\ldots,s_n$ such that every $s_i$ matches $R_1$.
    \end{enumerate}
\end{definition}

The following function implements matching in a straightforward way.
In our tests, it will essentially play the same role as the \texttt{evaluateDFA} and \texttt{evaluateNFA} functions,
and we will use it to check whether (supposedly) equivalent automata and regular expressions do accept/match the same strings.

\begin{code}
matches :: Eq symbol => [symbol] -> RegExp symbol -> Bool
matches str re = case re of
    Empty -> False
    Epsilon -> null str
    Literal l -> str == [l]
    Or re1 re2 -> matches str re1 || matches str re2
    Concat re1 re2 -> or [ matches str1 re1 && matches str2 re2 | (str1, str2) <- allSplittings str ] where 
        allSplittings s = [ splitAt k s | k <- [0..n] ] where n = length s
    Star re1 -> matches str Epsilon || or [ matches str1 re1 && matches str2 (Star re1) | (str1, str2) <- allNonEmptySplittings str ] where 
        allNonEmptySplittings s = [ splitAt k s | k <- [1..n] ] where n = length s 
\end{code}

Next, we implement a function to simplify regular expressions using some simple algebraic identities, 
that are stated as comments in the code for compactness.
Note that this function does not minimize a given regular expression\footnote{
    This is a very hard computational problem, and implementing a solution for it is outside the scope of our project.
} but it is useful, as a simple heuristic, in improving its readability,
especially for the regular expressions that we will obtain by converting NFAs.
Moreover, since the conversions are very inefficient and result in very large regular expressions,
simplifying them will help speed up the tests.
The \texttt{simplify} function works by repeatedly applying a simple one-step simplification function
until no further simplifications are possible.

\begin{code}
simplify :: Eq symbol => RegExp symbol -> RegExp symbol
simplify re -- repeatedly apply the one-step simplify function until a fixed point is reached
    | oneStepSimplify re == re = re 
    | otherwise = simplify $ oneStepSimplify re
    where
        oneStepSimplify :: Eq symbol => RegExp symbol -> RegExp symbol
        oneStepSimplify Empty = Empty
        oneStepSimplify Epsilon = Epsilon
        oneStepSimplify (Literal l) = Literal l
        oneStepSimplify (Or re1 re2) 
            | re1 == Empty = oneStepSimplify re2    -- Empty | re2 -> re2
            | re2 == Empty = oneStepSimplify re1  
            | re1 == re2 = oneStepSimplify re1      -- re1 | re1 -> re1
            | otherwise = Or (oneStepSimplify re1) (oneStepSimplify re2)
        oneStepSimplify (Concat re1 re2) 
            | re1 == Empty || re2 == Empty = Empty  -- Empty `Concat` re -> Empty
            | re1 == Epsilon = oneStepSimplify re2  -- Epsilon `Concat` re2 -> re2
            | re2 == Epsilon = oneStepSimplify re1
            | otherwise = Concat (oneStepSimplify re1) (oneStepSimplify re2)
        oneStepSimplify (Star re') = case re' of
            Empty -> Epsilon                                -- Empty* -> Epsilon
            Epsilon -> Epsilon                              -- Epsilon* -> Epsilon
            Or Epsilon re2 -> Star (oneStepSimplify re2)    -- (Epsilon | re2)* -> (re2)*
            Or re1 Epsilon -> Star (oneStepSimplify re1)
            Star re1 -> Star (oneStepSimplify re1)          -- ((re1)*)* -> (re1)*
            _ -> Star (oneStepSimplify re')
\end{code}

Finally, we implement a way to generate random regular expressions using QuickCheck.
We try to keep their size relatively small so that 
testing that converting back and forth from regular expressions to NFAs does not take too long.

\begin{code}
instance Arbitrary symbol => Arbitrary (RegExp symbol) where
  arbitrary :: Arbitrary symbol => Gen (RegExp symbol)
  arbitrary = sized randomRegExp where
    randomRegExp :: Int -> Gen (RegExp symbol)
    randomRegExp 0 = oneof [ Literal <$> (arbitrary :: Gen symbol), return Epsilon, return Empty ]
    randomRegExp n = oneof [ Literal <$> (arbitrary :: Gen symbol), return Epsilon 
                        , Or <$> randomRegExp (n `div` 10) <*> randomRegExp (n `div` 10)
                        , Concat <$> randomRegExp (n `div` 10) <*> randomRegExp (n `div` 10)
                        , Star <$> randomRegExp (n `div` 10)
                        ]
\end{code}