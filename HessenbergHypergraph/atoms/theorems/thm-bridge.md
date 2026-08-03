---
id: c32928ab3ec3
status: proved
type: theorem
lean:
  - decl: HessenbergDigraphs.digraph_model
    module: HessenbergDigraphs.Realization.DigraphModel
    line: 150
    state: proven
---

# Theorem — the support of a Givens product is the combinatorial digraph of its active set

Where the two halves of the theory meet. The matrix side and the combinatorial side are developed without reference to each other; this is the single statement that identifies them, and every later result is combinatorial.

## Statement

> [!theorem] Bridge
> For every [[def-unreduced-angle-vector|unreduced]] $\theta \in \Theta_n$, the [[def-support-digraph|support digraph]] of the [[def-givens-rotation|ordered Givens product]] is the [[def-active-set|combinatorial digraph]] of its active set:
> $$
> D\bigl(Q_n(\theta)\bigr) \;=\; D_n\bigl(S(\theta)\bigr).
> $$

## Proof

> [!note]- Proof (click to expand)
> Write $P_m = G_0(\theta_0) \cdots G_{m-1}(\theta_{m-1})$ for the partial products of [[def-givens-rotation|Givens rotations]], so $P_0 = I$ and $P_{n-1} = Q_n(\theta)$. Fix $i, j \in [n]$ and compare the entry $Q_n(\theta)_{ij}$ with the arc condition of the [[def-active-set|combinatorial digraph]]. There are three cases, and they are exactly the three shapes an index pair can have.
>
> **Below the subdiagonal: $j + 1 < i$.** Each $G_k(\theta_k)$ differs from the identity only in the $2 \times 2$ block at $(k, k{+}1)$, so a product of them in increasing order of $k$ has no entry below the first subdiagonal. Hence $Q_n(\theta)_{ij} = 0$. On the other side, the [[def-active-set|combinatorial digraph]] has no such arc either: a [[def-active-set|spine arc]] has $i = j+1$ and an overlay arc has $i \le j$. Both sides are empty.
>
> **On the subdiagonal: $i = j + 1$.** Multiplying out the product at this entry leaves the single factor $G_j(\theta_j)$ contributing its off-diagonal term, so $Q_n(\theta)_{j+1,\,j} = \sin\theta_j$, which is non-zero because $\theta$ is [[def-unreduced-angle-vector|unreduced]]. On the other side, $j+1 \to j$ is a spine arc, present for every $S$. Both sides hold.
>
> **On or above the diagonal: $i \le j$.** Here the claim is the equivalence
> $$
> Q_n(\theta)_{ij} \ne 0 \quad\Longleftrightarrow\quad i \in R(S(\theta)) \ \text{ and } \ j \in C(S(\theta)),
> $$
> whose two directions are proved separately, and it is the whole content of the theorem. Note first that by the definition of $S(\theta)$, membership unfolds to a statement about cosines: $i \in R(S(\theta))$ says $i = 1$ or $\cos\theta_{i-1} \ne 0$, and $j \in C(S(\theta))$ says $j = n$ or $\cos\theta_j \ne 0$.
>
> *Vanishing, contrapositive of $\Rightarrow$.* Suppose $i \notin R(S(\theta))$, that is $i \ne 1$ and $\cos\theta_{i-1} = 0$. A rotation with vanishing cosine is anti-diagonal in its block: it exchanges the two coordinates it acts on, up to a sign, and so carries basis vectors to basis vectors. Induct on $m$, showing that for $m \ge i$ every entry of $P_m$ in row $i$ and column $\ge i$ vanishes. For $m < i$ the row $i$ of $P_m$ is still that of the identity. At the step $m + 1 = i$ the factor $G_{i-1}(\theta_{i-1})$ enters with $\cos\theta_{i-1} = 0$, and its row $i$ has a single non-zero entry, in column $i-1$ — to the left of the range being tracked. Every later factor $G_m$ with $m \ge i$ acts on columns $m, m{+}1$, which the induction hypothesis has already zeroed in row $i$. Hence $Q_n(\theta)_{ij} = 0$ for all $j \ge i$. The argument for $j \notin C(S(\theta))$ — that is $j \ne n$ and $\cos\theta_j = 0$ — is the same one transposed, inducting down the column and using that $G_j(\theta_j)$ has a single non-zero entry in column $j$, in row $j+1$, below the range being tracked.
>
> *Propagation, direction $\Leftarrow$.* Suppose $i \in R(S(\theta))$ and $j \in C(S(\theta))$ and $i \le j$. The entry in row $i$ propagates rightwards along the partial products: for $m \ge i$,
> $$
> P_{m+1}(i, m{+}1) \;=\; -\sin\theta_m \cdot P_m(i, m),
> $$
> because column $m+1$ of $G_m(\theta_m)$ has its only relevant entry in row $m$. Since every $\sin\theta_m \ne 0$, induction from the base case $m = i$ — where $P_{i}(i,i) \ne 0$ precisely because $i \in R(S(\theta))$ makes the cosine at $i-1$ survive — gives $P_{m+1}(i, m{+}1) \ne 0$ for every $m \ge i$. Finally, column $j$ is *frozen* after step $j+1$: no factor $G_m$ with $m \ge j+1$ touches column $j$, so $Q_n(\theta)_{ij} = P_{j+1}(i,j)$. Combining, the entry is non-zero, the case $j = n$ being the one where the last column is reached with no further factor to disturb it.
>
> The three cases together identify the two digraphs arc by arc. $\square$

## Notes

> [!note]- Notes (click to expand)
> - ![[fig-q6-s24-support-pattern.svg]]
> - The two directions in the upper-triangular case are genuinely different arguments and neither is a rearrangement of the other. Vanishing is a statement that a *whole* row or column is zero, proved by induction on the partial products; propagation tracks a *single* entry as it moves right, and needs the unreduced hypothesis at every step. The vanishing half is where the hypothesis $i \le j$ is used, and the propagation half is where column freezing is.
> - The identity $P_{m+1}(i, m{+}1) = -\sin\theta_m \cdot P_m(i,m)$ is the reason the unreduced hypothesis cannot be weakened: a single $\sin\theta_m = 0$ breaks the chain at step $m$ and every overlay arc reaching past column $m$ disappears with it.
