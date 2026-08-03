---
id: e5e4010cc2e2
status: proved
type: theorem
lean:
  - decl: HessenbergDigraphs.card_isoClasses_quot
    module: HessenbergDigraphs.Combinatorial.ClassCount
    line: 268
    state: proven
  - decl: HessenbergDigraphs.count_formula
    module: HessenbergDigraphs.Combinatorial.Enumeration
    line: 61
    state: proven
---

# Theorem — the number of isomorphism classes

The classification made numerical. $2^{n-1}$ labelled configurations collapse by exactly the singleton coincidences of [[lem-singleton-isomorphism]] and by nothing else.

## Statement

> [!theorem] Connected count
> Let $n \ge 2$. The number of non-isomorphic weakly connected [[def-support-digraph|support digraphs]] of [[def-unreduced-angle-vector|unreduced]] [[def-orthogonal-upper-hessenberg|orthogonal upper Hessenberg]] matrices of size $n$ is
> $$
> N_n \;=\; 2^{\,n-1} \;-\; \Big\lfloor \frac{n-1}{2} \Big\rfloor.
> $$

## Proof

> [!note]- Proof (click to expand)
> By [[thm-classification]] the connected [[def-support-digraph|support digraphs]] are exactly the [[def-active-set|combinatorial digraphs]] $D_n(S)$ for $S \subseteq [n-1]$, giving $2^{n-1}$ labelled configurations. Split them by the size of $S$.
>
> - $|S| \ge 2$: by [[thm-rigidity]] distinct sets give non-isomorphic digraphs, so each is its own class. There are $\sum_{m=2}^{n-1}\binom{n-1}{m} = 2^{n-1} - n$ of them.
> - $S = \emptyset$: one digraph, the directed $n$-cycle, and one class.
> - $|S| = 1$: by [[lem-singleton-isomorphism]] the $n-1$ singletons $\{t\}$ fall into the classes $\{t, n-t\}$, of which there are $\lceil (n-1)/2 \rceil$.
>
> Summing,
> $$
> N_n = (2^{n-1} - n) + 1 + \Big\lceil \frac{n-1}{2} \Big\rceil = 2^{n-1} - \Big\lfloor \frac{n-1}{2} \Big\rfloor. \qquad \square
> $$
