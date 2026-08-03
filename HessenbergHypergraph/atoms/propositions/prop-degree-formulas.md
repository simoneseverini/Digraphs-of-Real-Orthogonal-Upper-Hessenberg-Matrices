---
id: f624a768ef59
status: proved
type: proposition
lean:
  - decl: HessenbergDigraphs.outDeg_first
    module: HessenbergDigraphs.Combinatorial.Degree
    line: 51
    state: proven
  - decl: HessenbergDigraphs.inDeg_last
    module: HessenbergDigraphs.Combinatorial.Degree
    line: 101
    state: proven
  - decl: HessenbergDigraphs.inDeg_mem_S
    module: HessenbergDigraphs.Combinatorial.Cut
    line: 52
    state: proven
---

# Proposition — in- and out-degrees of the combinatorial digraph

The arithmetic that makes the digraph legible. Reading off in-degrees identifies the elements of $S$ in order, which is how an isomorphism gets pinned to the identity in [[thm-rigidity]] and how the singleton exception is isolated in [[lem-singleton-isomorphism]].

## Statement

> [!proposition] Degree formulas
> Let $D = D_n(S)$ be the [[def-active-set|combinatorial digraph]] with $m := |S|$, and write $R = R(S)$, $C = C(S)$. Then $|R| = |C| = m + 1$, and
> $$
> \begin{aligned}
> d^{+}(1) &= m + 1, \\
> d^{+}(i) &= \begin{cases}
>   1 & \text{if } i > 1 \text{ and } i - 1 \notin S, \\
>   1 + |C \cap \{i, \dots, n\}| & \text{if } i > 1 \text{ and } i - 1 \in S,
> \end{cases} \\[1ex]
> d^{-}(j) &= \begin{cases}
>   1 & \text{if } j \in [n{-}1] \setminus S, \\
>   2 + |S \cap \{1, \dots, j{-}1\}| & \text{if } j \in S, \\
>   m + 1 & \text{if } j = n.
> \end{cases}
> \end{aligned}
> $$

## Proof

> [!note]- Proof (click to expand)
> The out-degree of $i > 1$ counts the spine arc to $i - 1$, plus the [[def-active-set|overlay]] arcs out of $i$, which exist precisely when $i \in R$ and then point to every $j \in C$ with $j \ge i$.
>
> The in-degree of $j < n$ counts the spine arc from $j + 1$, plus the overlay arcs into $j$, which exist precisely when $j \in C$ and then come from every $i \in R$ with $i \le j$.
>
> For $j = n$ there is no spine arc from $n + 1$, but every element of $R$ sends an overlay arc to $n$, so $d^{-}(n) = |R| = m + 1$. $\square$

## Notes

> [!note]- Notes (click to expand)
> - Writing $S = \{s_1 < \cdots < s_m\}$, the in-degrees on $C$ read $d^{-}(s_k) = k + 1$ and $d^{-}(n) = m + 1$, while every vertex outside $C$ has in-degree $1$. The in-degree sequence therefore recovers $S$ as an ordered set, which is exactly what [[thm-rigidity]] exploits.
