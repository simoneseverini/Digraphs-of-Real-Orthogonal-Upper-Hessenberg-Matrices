---
id: 9c87e4bd42ae
status: proved
type: theorem
lean:
  - decl: HessenbergDigraphs.OrthogonalHessenberg.exists_givensFactorization
    module: HessenbergDigraphs.Matrix.Givens.Factorization
    line: 840
    state: proven
---

# Theorem — every unreduced orthogonal upper Hessenberg matrix is a Givens product up to signs

The first half of the reduction: the class of matrices is no larger than the class of angle vectors. Together with [[thm-bridge]] it says that studying $D_n(S)$ costs nothing.

## Statement

> [!theorem] Universality
> Every [[def-unreduced-angle-vector|unreduced]] [[def-orthogonal-upper-hessenberg|orthogonal upper Hessenberg]] $Q \in \mathcal{H}_n$ is [[def-sign-equivalence|sign-equivalent]] to a canonical [[def-givens-rotation|Givens product]]: there exists $\theta \in \Theta_n$ with
> $$
> Q \;\simeq_{\mathrm{sign}}\; Q_n(\theta).
> $$

## Proof

> [!note]- Proof (click to expand)
> Induction on $n$. For $n \le 1$ there is nothing to factor and the empty product serves. So let $n \ge 2$ and let $Q$ be orthogonal [[def-orthogonal-upper-hessenberg|upper Hessenberg]].
>
> **The last row has two entries and unit norm.** Upper Hessenberg kills $Q_{n,j}$ for $j + 1 < n$, so the only entries of row $n$ that may be non-zero are $Q_{n,n-1}$ and $Q_{n,n}$. Reading the $(n,n)$ entry of $QQ^\top = I$ gives $\sum_j Q_{n,j}^2 = 1$, hence
> $$
> Q_{n,n-1}^2 + Q_{n,n}^2 = 1.
> $$
>
> **A rotation that clears it.** A pair $(a,b)$ with $a^2 + b^2 = 1$ is $(\sin\theta_0, \cos\theta_0)$ for some real $\theta_0$ — take $\theta_0 = \arccos b$, which gives $\cos\theta_0 = b$ and $\sin\theta_0 = \sqrt{1-b^2} = |a|$, and negate it when $a < 0$. Apply this to $a = Q_{n,n-1}$, $b = Q_{n,n}$ and set
> $$
> M \;=\; Q \cdot G_{n-2}(\theta_0)^\top .
> $$
> Computing row $n$ of the product with these values of $\cos\theta_0$ and $\sin\theta_0$ gives $M_{n,j} = 0$ for $j < n$ and $M_{n,n} = 1$; that is, the last row of $M$ is $e_n^\top$.
>
> **Orthogonality then clears the last column too.** $M$ is orthogonal, being a product of orthogonal matrices. Reading the $(i,n)$ entry of $MM^\top = I$ and using that row $n$ of $M$ is $e_n^\top$ collapses the sum to the single term $M_{i,n}$, giving $M_{i,n} = 0$ for $i < n$ and $M_{n,n} = 1$. So the last column is $e_n$ as well, and $M$ is block-diagonal.
>
> **The corner inherits both hypotheses.** $M$ is still upper Hessenberg: the entries of $Q \cdot G_{n-2}(\theta_0)^\top$ below the first subdiagonal are sums over columns $n-2$ and $n-1$ only, and for $j + 1 < i$ those indices are out of range. With the last row and column stripped, the principal $(n{-}1) \times (n{-}1)$ corner $M'$ is therefore orthogonal — the orthogonality sums restricted to the corner are the full ones, the missing terms being zero — and upper Hessenberg. The induction hypothesis applies to $M'$.
>
> **Assembling.** The hypothesis returns angles $\theta'$ and [[def-sign-equivalence|signature matrices]] $D_{L'}, D_{R'}$ with $Q_{n-1}(\theta') = D_{L'} M' D_{R'}$. Extend $\theta'$ by $\theta_0$ in the last slot; the [[def-givens-rotation|Givens product]] over the extended vector peels as
> $$
> Q_n(\theta_{\mathrm{full}}) \;=\; P_{n-2}(\theta') \cdot G_{n-2}(\theta_0),
> $$
> where $P_{n-2}(\theta')$ is the corner's product embedded in dimension $n$. Extend $D_{L'}, D_{R'}$ by repeating their last diagonal entry in position $n$; the extension is still $\pm 1$ on every entry, and — this is the point of repeating rather than choosing a fresh sign — it is *constant on the pair $(n{-}1, n)$*, so it commutes with $G_{n-2}(\theta_0)$. Commuting the extended $D_{R'}$ past that factor and substituting the induction hypothesis turns the peeled product into $D_L \, Q \, D_R$ with both diagonals $\pm 1$-valued. That is $Q \simeq_{\mathrm{sign}} Q_n(\theta_{\mathrm{full}})$.
>
> Finally the angles produced are [[def-unreduced-angle-vector|unreduced]] when $Q$ is: sign-equivalence preserves the zero pattern by [[cor-sign-invariance-of-support-digraph]], and the $(k{+}1,k)$ entry of the Givens product is $\sin\theta_k$, so a vanishing $\sin\theta_k$ would force a vanishing subdiagonal entry of $Q$. $\square$

## Notes

> [!note]- Notes (click to expand)
> - The signs are not cosmetic and cannot be normalised away at the start. Each peel of the induction fixes a rotation only up to the sign of $(\sin\theta_0, \cos\theta_0)$, and those choices accumulate. What makes them collectible is that a diagonal of $\pm 1$ commutes with $G_k(\theta)$ exactly when it takes the same value at $k$ and $k+1$ — which is why the extension step repeats the corner diagonal's last entry instead of appending a free one.
> - The induction peels the *last* row rather than the first because upper Hessenberg is an asymmetric condition: the last row is the one the shape has already reduced to two entries.
