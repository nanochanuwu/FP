\section{Regular Expressions} \label{sec:RegExp}

\begin{definition}
    Fix an alphabet $\Sigma$. We say that $R$ is \emph{regular expression} over $\Sigma$ if:
    \begin{enumerate}[(i)]
        \item $R=a$ for some $a\in\Sigma$;
        \item $R=\varnothing$,
        \item $R=\varepsilon$,
        \item $R=R_1 \cup R_2$, where $R_1,R_2$ are regular expressions,
        \item $R=R_1 \cdot R_2$, where $R_1,R_2$ are regular expressions,
        \item $R=(R_1)^*$, where $R_1$ is a regular expression.
    \end{enumerate}
\end{definition}

It is also often useful to use the abbreviation $R^+ := R \cup R^*$. 

The following data type definition implements the \texttt{RegExp} type by closely following its formal definition.
Together with the binary union (\texttt{Or}) and concatenation (\texttt{Concat}) operators, we also define their $n$-ary versions for convenience.
Finally, we implement a function for displaying regular expressions in a more readable format\footnote{
    This technically operates under the assumption that the alphabet does not contain \texttt{*} or \texttt{+} or the parentheses symbols,
    which would make the \texttt{prettyPrint} output ambiguous. Since the only purpose of this function is to display regular expressions in a readable format,
    however, we choose to simply ignore the issue.}.

\begin{code}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}

module RegExp where

import Test.QuickCheck ( Arbitrary(arbitrary), Gen, oneof, sized )

data RegExp sym = Empty
                | Epsilon
                | Literal sym
                | Or (RegExp sym) (RegExp sym)
                | Concat (RegExp sym) (RegExp sym)
                | Star (RegExp sym)
                deriving (Eq,Show)

oneOrMore :: RegExp sym -> RegExp sym
oneOrMore re = re `Concat` Star re

orAll :: [RegExp sym] -> RegExp sym
orAll = foldr Or Empty

concatAll :: [RegExp sym] -> RegExp sym 
concatAll = foldr Concat Epsilon

prettyPrint :: Show sym => RegExp sym -> String
prettyPrint re = case re of
    Empty -> "\2205"                                            -- unicode for \varnothing
    Epsilon -> "\0949"                                          -- unicode for \varepsilon
    Literal l -> show l
    Or re1 re2 -> "(" ++ prettyPrint re1 ++ "|" ++ prettyPrint re2 ++ ")"
    Concat re1 re2 -> prettyPrint re1 ++ prettyPrint re2
    Star re1 -> "(" ++ prettyPrint re1 ++ ")*"
\end{code}

% matching

\begin{code}
matches :: Eq sym => [sym] -> RegExp sym -> Bool
matches str re = case re of
    Empty -> False
    Epsilon -> null str
    Literal l -> str == [l]
    Or re1 re2 -> matches str re1 || matches str re2
    Concat re1 re2 -> or [ matches str1 re1 && matches str2 re2 | (str1, str2) <- allSplittings str ] where 
        allSplittings s = [ splitAt k s | k <- [0..n] ] where n = length s
    Star re1 -> matches str Epsilon || or [ matches str1 re1 && matches str2 re1 | (str1, str2) <- allNonEmptySplittings str ] where 
        allNonEmptySplittings s = [ splitAt k s | k <- [1..n] ] where n = length s 
\end{code}

% algebra of regular expressions. maybe insert explanations in-between code blocks?
% todo: find appropriate reference

\begin{code}
simplify :: Eq sym => RegExp sym -> RegExp sym
simplify re -- repetedly apply the one-step simplification function until a fixed point is reached
    | oneStepSimplify re == re = re
    | otherwise = simplify $ oneStepSimplify re
    where 
        oneStepSimplify Empty = Empty
        oneStepSimplify Epsilon = Epsilon
        oneStepSimplify (Literal l) = Literal l
        oneStepSimplify (Or re1 re2) 
            | re1 == Empty = re2
            | re2 == Empty = re1
            | re1 == re2 = oneStepSimplify re1
            | otherwise = Or (oneStepSimplify re1) (oneStepSimplify re2)
        oneStepSimplify (Concat re1 re2) 
            | re1 == Empty || re2 == Empty = Empty
            | re1 == Epsilon = re2
            | re2 == Epsilon = re1
            | otherwise = Concat (oneStepSimplify re1) (oneStepSimplify re2)
        oneStepSimplify (Star re') = case re' of
            Empty -> Epsilon
            Epsilon -> Epsilon
            Or Epsilon re2 -> Star (oneStepSimplify re2)
            Or re1 Epsilon -> Star (oneStepSimplify re1)
            _ -> Star (oneStepSimplify re)
\end{code}

Finally, we implement a way to generate random regular expressions using QuickCheck. 

\begin{code}
instance Arbitrary sym => Arbitrary (RegExp sym) where
  arbitrary :: Arbitrary sym => Gen (RegExp sym)
  arbitrary = sized randomRegExp where
    randomRegExp :: Int -> Gen (RegExp sym)
    randomRegExp 0 = oneof [ Literal <$> (arbitrary :: Gen sym), return Epsilon, return Empty ]
    randomRegExp n = oneof [ Literal <$> (arbitrary :: Gen sym), return Epsilon 
                        , Or <$> randomRegExp (n `div` 2) <*> randomRegExp (n `div` 2)
                        , Concat <$> randomRegExp (n `div` 2) <*> randomRegExp (n `div` 2)
                        , Star <$> randomRegExp (n `div` 2)
                        ]
\end{code}