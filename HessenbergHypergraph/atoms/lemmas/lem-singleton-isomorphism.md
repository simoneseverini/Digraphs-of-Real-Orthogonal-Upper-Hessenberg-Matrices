---
id: 6998f627078f
status: proved
type: lemma
lean:
  - decl: HessenbergDigraphs.singleton_iso
    module: HessenbergDigraphs.Combinatorial.Singleton.Iso
    line: 90
    state: proven
  - decl: HessenbergDigraphs.singleton_iso_unique
    module: HessenbergDigraphs.Combinatorial.Singleton.Iso
    line: 241
    state: proven
---

# Lemma — the singleton digraphs, and their only coincidence

The exception to rigidity, stated exactly. A one-element active set gives a cycle with two chords, and rotating the cycle carries $\{t\}$ to $\{n-t\}$. Nothing else coincides, which is why the count in [[thm-enumeration]] loses exactly $\lfloor (n-1)/2 \rfloor$.

## Statement

> [!lemma] Singleton isomorphisms
> Let $t \in [n-1]$ and write $D_{n,t} := D_n(\{t\})$ for the [[def-active-set|combinatorial digraph]] of the singleton $\{t\}$. Then
> $$
> D_{n,t} \;\cong\; D_{n,\,n-t},
> $$
> and if $D_{n,t} \cong D_{n,t'}$ then $\{t, n - t\} = \{t', n - t'\}$.

## Proof

> [!note]- Proof (click to expand)
> $D_{n,t}$ is the Hamilton cycle $H$ together with two [[def-active-set|overlay arcs]] — call them chords — namely $1 \to t$ and $(t{+}1) \to n$.
>
> **The isomorphism.** Let $\rho$ be the rotation $\rho(i) = i - 1$ for $i > 1$ and $\rho(1) = n$. Then $\rho^t$ carries $1 \to t$ to $(n{-}t{+}1) \to n$ and carries $(t{+}1) \to n$ to $1 \to (n{-}t)$. These are exactly the two chords of $D_{n,\,n-t}$, and $\rho$ preserves $H$, so $\rho^t$ is an isomorphism $D_{n,t} \to D_{n,\,n-t}$.
>
> **No other coincidence.** By [[prop-degree-formulas]] the vertices of in-degree $2$ in $D_{n,t}$ are precisely $t$ and $n$; all others have in-degree $1$. By [[lem-unique-hamilton-cycle]] any isomorphism preserves $H$ and hence directed distances along it. The two arcs of $H$ between $n$ and $t$ have lengths $t$ and $n - t$, so the unordered pair $\{t, n-t\}$ is an isomorphism invariant. Therefore $D_{n,t} \cong D_{n,t'}$ forces $\{t, n-t\} = \{t', n-t'\}$. $\square$
