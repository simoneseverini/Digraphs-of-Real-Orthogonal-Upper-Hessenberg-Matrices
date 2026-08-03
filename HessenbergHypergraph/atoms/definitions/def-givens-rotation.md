---
id: cf1c4b441946
type: definition
lean:
  - decl: Matrix.givensRotation
    module: HessenbergDigraphs.Matrix.Givens.Rotation
    line: 67
    state: proven
  - decl: Matrix.givensProduct
    module: HessenbergDigraphs.Matrix.Givens.Product
    line: 69
    state: proven
---

# Definition — Givens rotation, ordered Givens product

The generators. A Givens rotation turns one plane and leaves the rest of space alone; taking one for each adjacent pair of coordinates, in order, produces a matrix that is automatically [[def-orthogonal-upper-hessenberg|orthogonal upper Hessenberg]]. [[thm-universality]] says every such matrix arises this way.

## Statement

> [!definition] Givens rotation, ordered Givens product
> For $k \in \{0, \dots, n-2\}$ and $\theta \in \mathbb{R}$, the *Givens rotation* $G_k(\theta) \in \mathbb{R}^{n \times n}$ is the identity with the $2 \times 2$ block at rows and columns $(k, k{+}1)$ replaced by $\left[\begin{smallmatrix}\cos\theta & -\sin\theta\\ \sin\theta & \cos\theta\end{smallmatrix}\right]$.
>
> The *ordered Givens product* of an angle vector $\theta = (\theta_0, \dots, \theta_{n-2})$ is
> $$
> Q_n(\theta) \;:=\; G_0(\theta_0)\, G_1(\theta_1)\,\cdots\,G_{n-2}(\theta_{n-2}).
> $$
> It is orthogonal [[def-orthogonal-upper-hessenberg|upper Hessenberg]], and its $(k{+}1, k)$ subdiagonal entry equals $\sin\theta_k$.
