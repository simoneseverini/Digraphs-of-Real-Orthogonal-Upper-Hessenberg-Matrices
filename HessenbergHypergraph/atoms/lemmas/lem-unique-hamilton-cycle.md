---
id: 4b4e6a05d440
status: proved
type: lemma
lean:
  - decl: HessenbergDigraphs.hcycle_subset
    module: HessenbergDigraphs.Combinatorial.Hamilton
    line: 50
    state: proven
  - decl: HessenbergDigraphs.cut_lemma
    module: HessenbergDigraphs.Combinatorial.Cut
    line: 37
    state: proven
---

# Lemma — the spine is the only directed Hamilton cycle

What pins the labelling down. A digraph isomorphism may permute vertices arbitrarily, but it must carry Hamilton cycles to Hamilton cycles — and there is only one, so it acts as a rotation along it. Every later rigidity argument is about which rotation.

## Statement

> [!lemma] Unique Hamilton cycle
> Let $n \ge 2$ and $S \subseteq [n-1]$. The [[def-active-set|combinatorial digraph]] $D_n(S)$ contains exactly one directed Hamilton cycle, namely
> $$
> H \;=\; 1 \to n \to n{-}1 \to \cdots \to 2 \to 1.
> $$

## Proof

> [!note]- Proof (click to expand)
> Fix $k \in [n-1]$ and consider the directed cut from $V_{>k} = \{k{+}1, \dots, n\}$ to $V_{\le k} = \{1, \dots, k\}$. By [[lem-cut]] the only arc crossing it is the [[def-active-set|spine arc]] $(k{+}1) \to k$.
>
> A directed Hamilton cycle visits both sides of the cut, so it crosses it at least once, and therefore uses $(k{+}1) \to k$. As $k$ ranges over $[n-1]$ this forces the whole path $n \to n{-}1 \to \cdots \to 1$. To close the cycle the arc $1 \to n$ is required; it is present, since $1 \in R(S)$ and $n \in C(S)$ with $1 \le n$. Hence $H$ is a Hamilton cycle and it is the only one. $\square$
