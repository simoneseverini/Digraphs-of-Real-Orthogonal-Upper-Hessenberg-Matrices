---
id: 7fc752ea560c
status: proved
type: example
lean:
  - decl: HessenbergDigraphs.example_D5_S13
    module: HessenbergDigraphs.PaperExamples
    line: 186
    state: proven
---

# Example — $D_5(\{1,3\})$, a rigid two-element set with one loop

A case where [[thm-rigidity]] applies: no other active set of size $\ge 2$ gives an isomorphic digraph. It also shows a loop, at the single vertex of $R \cap C$.

## Statement

> [!example] $n = 5$, $S = \{1,3\}$
> The angle vector $\theta = (\pi/4, \pi/2, \pi/4, \pi/2)$ gives
> $$
> Q = \begin{pmatrix}
> \tfrac{1}{\sqrt{2}} & 0 & \tfrac{1}{2} & 0 & \tfrac{1}{2} \\
> -\tfrac{1}{\sqrt{2}} & 0 & \tfrac{1}{2} & 0 & \tfrac{1}{2} \\
> 0 & -1 & 0 & 0 & 0 \\
> 0 & 0 & -\tfrac{1}{\sqrt{2}} & 0 & \tfrac{1}{\sqrt{2}} \\
> 0 & 0 & 0 & -1 & 0
> \end{pmatrix},
> \qquad
> A = \begin{pmatrix}
> 1 & 0 & 1 & 0 & 1 \\
> 1 & 0 & 1 & 0 & 1 \\
> 0 & 1 & 0 & 0 & 0 \\
> 0 & 0 & 1 & 0 & 1 \\
> 0 & 0 & 0 & 1 & 0
> \end{pmatrix}.
> $$
> Here $R \cap C = \{1\}$, so by [[lem-loops-in-model]] there is exactly one self-loop, at vertex $1$.

## Proof

> [!note]- Verification (click to expand)
> With $\theta = (\pi/4, \pi/2, \pi/4, \pi/2)$ indexed by $k = 0, \dots, 3$:
> $$
> \sin\theta = \bigl(\tfrac{1}{\sqrt2}, 1, \tfrac{1}{\sqrt2}, 1\bigr), \qquad \cos\theta = \bigl(\tfrac{1}{\sqrt2}, 0, \tfrac{1}{\sqrt2}, 0\bigr).
> $$
> Every $\sin\theta_k$ is non-zero, so $\theta \in \Theta_5$. The indices with $\cos\theta_k \ne 0$ are $k \in \{0, 2\}$, so $S(\theta) = \{1, 3\}$, and
> $$
> R = \{1\} \cup \{2, 4\} = \{1,2,4\}, \qquad C = \{1,3\} \cup \{5\} = \{1,3,5\}.
> $$
> Hence $R \cap C = \{1\}$, and [[lem-loops-in-model]] gives exactly one loop, at vertex $1$.
>
> The overlay arcs are the pairs $i \in R$, $j \in C$ with $i \le j$: $1 \to 1$, $1 \to 3$, $1 \to 5$, $2 \to 3$, $2 \to 5$, $4 \to 5$. With the spine $2 \to 1$, $3 \to 2$, $4 \to 3$, $5 \to 4$ these are exactly the non-zero entries of $A$ above.
>
> Since $|S| = 2$, [[thm-rigidity]] applies: no other [[def-active-set|active set]] of size at least two has an isomorphic digraph. $\square$

## Notes

> [!note]- Notes (click to expand)
> - ![[fig-d5-s13.svg]]
