---
id: eff425b90fb0
status: proved
type: theorem
lean:
  - decl: HessenbergDigraphs.card_looplessClasses_quot
    module: HessenbergDigraphs.Combinatorial.ClassCount
    line: 526
    state: proven
  - decl: HessenbergDigraphs.count_loopless_formula
    module: HessenbergDigraphs.Combinatorial.Enumeration
    line: 159
    state: proven
---

# Theorem — the number of loopless isomorphism classes

The same count restricted to digraphs without self-loops. The restriction turns the power of two into a Fibonacci number, because [[cor-loopless-characterization]] converts "loopless" into "no two consecutive elements".

## Statement

> [!theorem] Loopless count
> Let $n \ge 3$. The number of non-isomorphic loopless connected [[def-support-digraph|support digraphs]] of [[def-unreduced-angle-vector|unreduced]] [[def-orthogonal-upper-hessenberg|orthogonal upper Hessenberg]] matrices of size $n$ is
> $$
> N_n^{\mathrm{loopless}} \;=\; F_{n-1} \;-\; \Big\lfloor \frac{n-3}{2} \Big\rfloor,
> $$
> where $F_k$ is the $k$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$, $F_{m+2} = F_{m+1} + F_m$).

## Proof

> [!note]- Proof (click to expand)
> By [[cor-loopless-characterization]] the loopless connected digraphs are the [[def-active-set|combinatorial digraphs]] $D_n(S)$ for $S \subseteq \{2, \dots, n-2\}$ with no two consecutive elements. The subsets of a set of $m$ consecutive integers containing no two consecutive elements number $F_{m+2}$; here $m = n - 3$, giving $F_{n-1}$ labelled configurations.
>
> Counting classes as in [[thm-enumeration]]: subsets with $|S| \ge 2$ are rigid by [[thm-rigidity]] and each is its own class; the empty set gives one class; the $n-3$ singletons fall into $\lceil (n-3)/2 \rceil$ classes by [[lem-singleton-isomorphism]]. Summing,
> $$
> N_n^{\mathrm{loopless}} = \bigl(F_{n-1} - (n-3) - 1\bigr) + \Big\lceil \frac{n-3}{2} \Big\rceil + 1 = F_{n-1} - \Big\lfloor \frac{n-3}{2} \Big\rfloor. \qquad \square
> $$
