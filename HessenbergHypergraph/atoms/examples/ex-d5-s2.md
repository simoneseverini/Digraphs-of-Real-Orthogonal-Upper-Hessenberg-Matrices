---
id: b78815e6aa25
status: proved
type: example
lean:
  - decl: HessenbergDigraphs.example_D5_S2
    module: HessenbergDigraphs.PaperExamples
    line: 131
    state: proven
---

# Example — $D_5(\{2\})$, a loopless singleton

The smallest interesting case, and the one where rigidity fails: by [[lem-singleton-isomorphism]], $D_5(\{2\}) \cong D_5(\{3\})$.

## Statement

> [!example] $n = 5$, $S = \{2\}$
> The angle vector $\theta = (\pi/2, \pi/4, \pi/2, \pi/2)$ gives
> $$
> Q = \begin{pmatrix}
> 0 & \tfrac{1}{\sqrt{2}} & 0 & 0 & \tfrac{1}{\sqrt{2}} \\
> -1 & 0 & 0 & 0 & 0 \\
> 0 & -\tfrac{1}{\sqrt{2}} & 0 & 0 & \tfrac{1}{\sqrt{2}} \\
> 0 & 0 & -1 & 0 & 0 \\
> 0 & 0 & 0 & -1 & 0
> \end{pmatrix},
> \qquad
> A = \begin{pmatrix}
> 0 & 1 & 0 & 0 & 1 \\
> 1 & 0 & 0 & 0 & 0 \\
> 0 & 1 & 0 & 0 & 1 \\
> 0 & 0 & 1 & 0 & 0 \\
> 0 & 0 & 0 & 1 & 0
> \end{pmatrix},
> $$
> where $A$ is the adjacency matrix of the [[def-support-digraph|support digraph]]. The Hamilton cycle is $1 \to 5 \to 4 \to 3 \to 2 \to 1$, and $R = \{1,3\}$, $C = \{2,5\}$ are disjoint, so the digraph is loopless.

## Proof

> [!note]- Verification (click to expand)
> With $\theta = (\pi/2, \pi/4, \pi/2, \pi/2)$ indexed by $k = 0, \dots, 3$:
> $$
> \sin\theta = \bigl(1, \tfrac{1}{\sqrt2}, 1, 1\bigr), \qquad \cos\theta = \bigl(0, \tfrac{1}{\sqrt2}, 0, 0\bigr).
> $$
> Every $\sin\theta_k$ is non-zero, so $\theta \in \Theta_5$. Only $\cos\theta_1 \ne 0$, so $S(\theta) = \{2\}$, and $R = \{1, 3\}$, $C = \{2, 5\}$. They are disjoint, so [[lem-loops-in-model]] gives no loops.
>
> The arcs of $D_5(\{2\})$ are the spine $2 \to 1$, $3 \to 2$, $4 \to 3$, $5 \to 4$, together with the [[def-active-set|overlay arcs]] $i \to j$ for $i \in \{1,3\}$, $j \in \{2,5\}$, $i \le j$ — that is $1 \to 2$, $1 \to 5$ and $3 \to 5$. Reading these off row by row gives exactly the matrix $A$ displayed above, which by [[thm-bridge]] is the support pattern of $Q$.
>
> The spine arcs traversed backwards are the Hamilton cycle $1 \to 5 \to 4 \to 3 \to 2 \to 1$ of [[lem-unique-hamilton-cycle]]. $\square$

## Notes

> [!note]- Notes (click to expand)
> - ![[fig-d5-s2.svg]]
> - $A$ is exactly the pattern [[thm-bridge]] predicts.
