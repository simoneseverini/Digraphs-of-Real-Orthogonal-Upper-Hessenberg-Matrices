---
topic: hessenberg-digraphs
type: topic
section: "03"
date: 2026-08-02
tags: [digraphs, enumeration, fibonacci]
---
# Loopless digraphs

The count again, restricted to digraphs with no self-loop — where the power of two becomes a Fibonacci number.

A self-loop in the support digraph records a non-zero diagonal entry. Whether one occurs at a given vertex is decided by the active set alone, and the condition is local enough to be read backwards: the loopless digraphs are exactly those whose active set avoids both endpoints and never contains two consecutive elements. Counting those is a classical Fibonacci problem, which is why the same argument as in [[02-isomorphism-classes-and-enumeration|the previous chapter]] lands on a different sequence.

## Where a loop can sit

An overlay arc $i \to j$ needs $i \le j$, so a loop is an overlay arc with $i = j$ — never a spine arc. It exists exactly where an active row coincides with an active column.

![[lem-loops-in-model]]

The three cases are the same statement read at the two endpoints and in the middle. At vertex $1$ the active-row condition is automatic, at vertex $n$ the active-column condition is; only in the interior are two conditions genuinely required, and there they ask for consecutive elements.

![[cor-loopless-characterization]]

## The Fibonacci count

The subsets of $m$ consecutive integers with no two consecutive elements number $F_{m+2}$. Here the available range is $\{2, \dots, n-2\}$, of size $n-3$, so there are $F_{n-1}$ loopless active sets — and then the collapse into isomorphism classes runs exactly as before, since [[thm-rigidity]] and [[lem-singleton-isomorphism]] are indifferent to whether loops are present.

![[thm-loopless-enumeration]]

## Two small cases

The $5 \times 5$ examples show both sides of the loop condition. In the first, $R$ and $C$ are disjoint and there is no loop; in the second they meet in one vertex, and there is exactly one.

![[ex-d5-s2]]

![[fig-d5-s2.svg]]

*The loopless support digraph $D_5(\{2\})$. Active rows $R = \{1,3\}$ (blue fill) and active columns $C = \{2,5\}$ (red outline) are disjoint.*

![[ex-d5-s13]]

![[fig-d5-s13.svg]]

*The support digraph $D_5(\{1,3\})$. Since $R \cap C = \{1\}$, there is exactly one self-loop, at vertex $1$.*
