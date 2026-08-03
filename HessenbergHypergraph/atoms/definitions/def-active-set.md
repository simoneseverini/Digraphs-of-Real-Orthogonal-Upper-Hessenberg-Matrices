---
id: c12be3cf56b2
type: definition
lean:
  - decl: HessenbergDigraphs.ActiveSet
    module: HessenbergDigraphs.ActiveSet
    line: 70
    state: proven
  - decl: HessenbergDigraphs.ActiveSet.digraph
    module: HessenbergDigraphs.ActiveSet
    line: 281
    state: proven
  - decl: HessenbergDigraphs.Arc
    module: HessenbergDigraphs.Combinatorial.Arc
    line: 61
    state: proven
---

# Definition — active set, active rows and columns, combinatorial digraph

The combinatorial side of the classification, defined without reference to any matrix. A subset $S$ of $[n-1]$ determines a digraph $D_n(S)$: a directed Hamilton cycle — the *spine* — with *overlay* arcs laid over it. The content of [[thm-bridge]] is that this is exactly what matrix supports look like.

## Statement

> [!definition] Active set, combinatorial digraph
> An *active set* is any subset $S \subseteq [n-1]$. From $S$ derive the *active rows* and *active columns*
> $$
> R(S) \;:=\; \{1\} \cup \{k+1 : k \in S\}, \qquad C(S) \;:=\; S \cup \{n\},
> $$
> and the *combinatorial digraph* $D_n(S)$ on $[n]$, whose arcs are of two kinds:
> - *spine* arcs $j+1 \to j$ for $1 \le j \le n-1$;
> - *overlay* arcs $i \to j$ whenever $i \in R(S)$, $j \in C(S)$ and $i \le j$.
>
> For an [[def-unreduced-angle-vector|unreduced]] $\theta \in \Theta_n$, the *active set of an angle vector* is
> $$
> S(\theta) \;:=\; \bigl\{\, k+1 \,:\, k \in \{0, \dots, n-2\},\ \cos\theta_k \ne 0 \,\bigr\} \;\subseteq\; [n-1].
> $$

## Notes

> [!note]- Notes (click to expand)
> - $D_n(S)$ uses the set $S$ alone; no matrix and no angle vector enters its construction. That separation is why the combinatorial theory and the matrix theory can be developed independently and meet only at [[thm-bridge]].
> - $|R(S)| = |C(S)| = |S| + 1$; see [[prop-degree-formulas]].
> - ![[fig-d6-s24-anatomy.svg]]
