---
id: f3c6abb76798
type: definition
lean:
  - decl: HessenbergDigraphs.UnreducedAngles
    module: HessenbergDigraphs.Matrix.UnreducedAngles
    line: 68
    state: proven
---

# Definition — unreduced angle vector

The non-degeneracy hypothesis every theorem here carries. A vanishing subdiagonal entry splits the matrix into two independent blocks; ruling that out is what keeps the support digraph connected and its Hamilton cycle intact.

## Statement

> [!definition] Unreduced angle vector
> An angle vector $\theta = (\theta_0, \dots, \theta_{n-2})$ is *unreduced* if $\sin\theta_k \ne 0$ for every $k$ — equivalently, if every subdiagonal entry of the [[def-givens-rotation|ordered Givens product]] $Q_n(\theta)$ is non-zero. We write $\Theta_n$ for the set of unreduced angle vectors.
