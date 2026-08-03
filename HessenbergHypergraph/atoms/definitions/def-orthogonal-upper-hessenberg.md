---
id: 7618962d7afd
type: definition
lean:
  - decl: HessenbergDigraphs.OrthogonalHessenberg
    module: HessenbergDigraphs.Matrix.OrthogonalHessenberg
    line: 67
    state: proven
---

# Definition — orthogonal upper Hessenberg matrix

The class the whole classification is about. Upper Hessenberg is a sparsity condition — everything below the first subdiagonal vanishes — and orthogonality is a rigidity condition. Neither alone is restrictive; together they force the matrix to be a product of plane rotations, and that is what makes the support pattern computable.

## Statement

> [!definition] Orthogonal upper Hessenberg matrix
> A matrix $Q \in \mathbb{R}^{n \times n}$ is *upper Hessenberg* if $Q_{ij} = 0$ whenever $j + 1 < i$, and *orthogonal* if $Q^\top Q = I$. We write $\mathcal{H}_n$ for the set of orthogonal upper Hessenberg matrices in $\mathbb{R}^{n \times n}$.
