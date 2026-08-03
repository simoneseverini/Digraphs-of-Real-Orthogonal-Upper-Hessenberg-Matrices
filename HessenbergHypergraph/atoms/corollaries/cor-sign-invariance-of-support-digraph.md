---
id: acdc4ce937fa
status: proved
type: corollary
lean:
  - decl: Matrix.supportDigraph_eq_of_signEquiv
    module: HessenbergDigraphs.Matrix.SignEquivalence
    line: 184
    state: proven
---

# Corollary — the support digraph is a sign-equivalence invariant

Why normalising signs is free. The classification may replace a matrix by any sign-equivalent one without changing the object being classified.

## Statement

> [!corollary] Sign-invariance of the support digraph
> [[def-sign-equivalence|Sign-equivalent]] matrices have identical zero / non-zero patterns; hence $D(Q) = D(Q')$ whenever $Q \simeq_{\mathrm{sign}} Q'$.

## Proof

> [!note]- Proof (click to expand)
> If $Q' = D_L Q D_R$ with $D_L, D_R$ [[def-sign-equivalence|signature matrices]], then $Q'_{ij} = (D_L)_{ii}\, Q_{ij}\, (D_R)_{jj}$ with both factors equal to $\pm 1$. So $Q'_{ij} = 0$ if and only if $Q_{ij} = 0$, and the [[def-support-digraph|support digraphs]] coincide. $\square$
