---
id: 996a782326e4
status: proved
type: example
lean:
  - decl: HessenbergDigraphs.example_D6_S24
    module: HessenbergDigraphs.PaperExamples
    line: 67
    state: proven
---

# Example — $D_6(\{2,4\})$, the anatomy of the model

The picture to hold on to. Spine and overlay are visible separately, the active rows and columns are marked, and $R \cap C = \emptyset$ so there are no loops to complicate it.

## Statement

> [!example] $n = 6$, $S = \{2,4\}$
> The angle vector $\theta = (\pi/2, \pi/4, \pi/2, \pi/4, \pi/2)$ has $\cos\theta_k \ne 0$ exactly for $k \in \{1, 3\}$, so its [[def-active-set|active set]] is $S = \{2, 4\}$, with
> $$
> R = \{1, 3, 5\}, \qquad C = \{2, 4, 6\}.
> $$
> Since $R \cap C = \emptyset$, the digraph $D_6(\{2,4\})$ has no self-loops.

## Proof

> [!note]- Verification (click to expand)
> With $\theta = (\pi/2, \pi/4, \pi/2, \pi/4, \pi/2)$ indexed by $k = 0, \dots, 4$:
> $$
> \sin\theta = \bigl(1, \tfrac{1}{\sqrt2}, 1, \tfrac{1}{\sqrt2}, 1\bigr), \qquad \cos\theta = \bigl(0, \tfrac{1}{\sqrt2}, 0, \tfrac{1}{\sqrt2}, 0\bigr).
> $$
> Every $\sin\theta_k$ is non-zero, so $\theta \in \Theta_6$ is [[def-unreduced-angle-vector|unreduced]]. The indices with $\cos\theta_k \ne 0$ are $k \in \{1, 3\}$, so $S(\theta) = \{k+1\} = \{2, 4\}$.
>
> Then $R = \{1\} \cup \{k+1 : k \in S\} = \{1\} \cup \{3, 5\} = \{1,3,5\}$ and $C = S \cup \{6\} = \{2,4,6\}$. These are disjoint, so by [[lem-loops-in-model]] the digraph has no loop at any vertex. $\square$

## Notes

> [!note]- Notes (click to expand)
> - ![[fig-d6-s24-anatomy.svg]]
> - The matrix-side counterpart is the support pattern of $Q_6(\{2,4\})$, which [[thm-bridge]] predicts entry by entry: ![[fig-q6-s24-support-pattern.svg]]
