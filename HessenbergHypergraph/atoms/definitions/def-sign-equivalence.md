---
id: d5f8f935741e
type: definition
lean:
  - decl: Matrix.SignEquiv
    module: HessenbergDigraphs.Matrix.SignEquivalence
    line: 71
    state: proven
---

# Definition — sign-equivalence

The equivalence that the support digraph cannot see. Flipping the sign of a row or a column changes the matrix and changes nothing about which entries are non-zero, so the classification is free to normalise signs away.

## Statement

> [!definition] Sign-equivalence
> Two matrices $Q, Q' \in \mathbb{R}^{n \times n}$ are *sign-equivalent*, written $Q \simeq_{\mathrm{sign}} Q'$, if $Q' = D_L\, Q\, D_R$ for some *signature matrices* $D_L, D_R$ — diagonal matrices whose diagonal entries are all $\pm 1$.
