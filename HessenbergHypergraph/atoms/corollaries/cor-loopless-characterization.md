---
id: 54ae2c2e3fb2
status: proved
type: corollary
lean:
  - decl: HessenbergDigraphs.loopless_iff
    module: HessenbergDigraphs.Combinatorial.Loop
    line: 134
    state: proven
---

# Corollary — loopless means no endpoints and no two consecutive elements

The loopless case restated as a condition on $S$ that can be counted. Subsets of an interval with no two consecutive elements are counted by Fibonacci numbers, which is where the second enumeration formula comes from.

## Statement

> [!corollary] Loopless characterization
> A connected [[def-support-digraph|support digraph]] $D(Q)$ is loopless if and only if $D(Q) = D_n(S)$ for the [[def-active-set|combinatorial digraph]] of a subset $S \subseteq \{2, \dots, n-2\}$ containing no two consecutive elements.

## Proof

> [!note]- Proof (click to expand)
> By [[lem-loops-in-model]], absence of a loop at $1$ forces $1 \notin S$ and absence of a loop at $n$ forces $n - 1 \notin S$, so $S \subseteq \{2, \dots, n-2\}$.
>
> Absence of a loop at an interior vertex $v \in \{2, \dots, n-1\}$ says that $v - 1 \in S$ and $v \in S$ do not both hold. Ranging over $v$, this says exactly that $S$ contains no two consecutive elements. $\square$
