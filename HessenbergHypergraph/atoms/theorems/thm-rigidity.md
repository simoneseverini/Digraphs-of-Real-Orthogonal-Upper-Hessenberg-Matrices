---
id: ecf15cbfb669
status: proved
type: theorem
lean:
  - decl: HessenbergDigraphs.rigid
    module: HessenbergDigraphs.Combinatorial.Rigidity
    line: 331
    state: proven
---

# Theorem — an active set of size at least two is recoverable from its digraph

The uniqueness half of the classification. Two different active sets of size $\ge 2$ give digraphs that are not merely different but non-isomorphic, so the isomorphism classes are in bijection with the sets themselves. The hypothesis $|S| \ge 2$ is sharp: [[lem-singleton-isomorphism]] is the failure.

## Statement

> [!theorem] Rigidity
> Let $S, S' \subseteq [n-1]$ with $|S| \ge 2$ and $|S'| \ge 2$. If the [[def-active-set|combinatorial digraphs]] satisfy $D_n(S) \cong D_n(S')$ as digraphs, then $S = S'$.

## Proof

> [!note]- Proof (click to expand)
> Let $m = |S| \ge 2$ and let $\Phi : D_n(S) \to D_n(S')$ be an isomorphism of [[def-active-set|combinatorial digraphs]].
>
> **$\Phi$ is a rotation.** By [[lem-unique-hamilton-cycle]] each digraph has exactly one directed Hamilton cycle. $\Phi$ carries the cycle $H$ of $D_n(S)$ to the cycle $H'$ of $D_n(S')$, so it acts as a cyclic rotation of the vertices along $H$ and preserves directed distances along it.
>
> **The in-degrees locate $S$.** Write $S = \{s_1 < \cdots < s_m\}$. By [[prop-degree-formulas]], $d^{-}(s_k) = k + 1$ for $1 \le k \le m$, $d^{-}(n) = m + 1$, and every other vertex has in-degree $1$. Since $m \ge 2$, the vertex $s_{m-1}$ is the unique vertex of in-degree exactly $m$, so $\Phi$ fixes it. The two vertices of maximum in-degree $m+1$ are $s_m$ and $n$, so $\Phi(\{s_m, n\}) = \{s'_m, n\}$.
>
> **$\Phi$ fixes $n$.** Suppose instead $\Phi(n) = s'_m$. Comparing directed distances along the Hamilton cycle from $n$ to $s_{m-1}$ and from $s_m$ to $s_{m-1}$ gives
> $$
> n - s_{m-1} = s'_m - s'_{m-1}, \qquad s_m - s_{m-1} = n - s'_{m-1}.
> $$
> Subtracting yields $s_m + s'_m = 2n$, which contradicts $s_m \le n-1$ and $s'_m \le n-1$.
>
> **Conclusion.** So $\Phi(n) = n$. A rotation fixing a vertex is the identity, and since directed distances from $n$ are preserved, $\Phi = \mathrm{id}$ and hence $S = S'$. $\square$
