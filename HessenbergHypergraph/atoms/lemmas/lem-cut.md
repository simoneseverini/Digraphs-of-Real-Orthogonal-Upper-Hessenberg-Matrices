---
id: ecc3e6bb7157
status: proved
type: lemma
lean:
  - decl: HessenbergDigraphs.cut_lemma
    module: HessenbergDigraphs.Combinatorial.Cut
    line: 37
    state: proven
---

# Lemma — the only arc crossing a downward cut is the spine arc

The one structural fact the whole rigidity argument rests on. Overlay arcs never decrease the index, so the digraph is almost acyclic: at every cut, a single arc goes the wrong way. That arc is forced, and everything that has to be preserved by an isomorphism is preserved because of it.

## Statement

> [!lemma] Cut lemma
> Let $n \ge 2$ and $S \subseteq [n-1]$. For every $k \in [n-1]$, the only arc of the [[def-active-set|combinatorial digraph]] $D_n(S)$ from $\{k{+}1, \dots, n\}$ to $\{1, \dots, k\}$ is the spine arc $(k{+}1) \to k$.

## Proof

> [!note]- Proof (click to expand)
> An arc of $D_n(S)$ is a spine arc or an [[def-active-set|overlay arc]]. An overlay arc $i \to j$ satisfies $i \le j$, so it never runs from a higher index to a strictly lower one and cannot cross the cut. Among the spine arcs $j+1 \to j$, exactly one has $j + 1 > k \ge j$, namely $j = k$. $\square$
