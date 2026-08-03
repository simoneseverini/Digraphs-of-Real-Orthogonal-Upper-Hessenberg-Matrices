---
id: 228c8f7bcd2d
status: proved
type: theorem
lean:
  - decl: HessenbergDigraphs.classification
    module: HessenbergDigraphs.Classification
    line: 54
    state: proven
---

# Theorem — classification of the support digraphs

What the network is for. Three statements, proved independently, that together say the support digraphs of unreduced orthogonal upper Hessenberg matrices are exactly the $D_n(S)$, and that $S$ is recoverable from the digraph whenever it has at least two elements.

## Statement

> [!theorem] Classification
> Fix $n \ge 2$. The [[def-support-digraph|support digraphs]] of [[def-unreduced-angle-vector|unreduced]] [[def-orthogonal-upper-hessenberg|orthogonal upper Hessenberg]] matrices are classified by the conjunction of:
> 1. *realizability* — every $S \subseteq [n-1]$ equals $S(\theta)$ for some $\theta \in \Theta_n$;
> 2. *bridge* — for every $\theta \in \Theta_n$, the support of the [[def-givens-rotation|Givens product]] $Q_n(\theta)$ equals the [[def-active-set|combinatorial digraph]] $D_n(S(\theta))$;
> 3. *rigidity* — for all $S, S'$ with $|S|, |S'| \ge 2$, $D_n(S) \cong D_n(S')$ implies $S = S'$.

## Proof

> [!note]- Proof (click to expand)
> Clause 2 is [[thm-bridge]] and clause 3 is [[thm-rigidity]].
>
> Clause 1 is witnessed explicitly: given $S \subseteq [n-1]$, set $\theta_k = \pi/4$ if $k + 1 \in S$ and $\theta_k = \pi/2$ otherwise. Then $\sin\theta_k \ne 0$ for every $k$, so $\theta$ is [[def-unreduced-angle-vector|unreduced]], while $\cos\theta_k \ne 0$ holds exactly when $k + 1 \in S$ — that is, $S(\theta) = S$. $\square$

## Notes

> [!note]- Notes (click to expand)
> - The statement is a packaging: it adds no mathematical content to its three components. It exists so that "the classification" has one address.
> - [[thm-universality]] is what makes the classification exhaustive rather than a statement about Givens products only: every unreduced matrix in $\mathcal{H}_n$ is sign-equivalent to some $Q_n(\theta)$, and by [[cor-sign-invariance-of-support-digraph]] the support digraph does not see the difference.
