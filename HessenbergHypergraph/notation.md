---
type: notation
---
# Notation

Every symbol used in a Statement or Proof of this pool, with the card that defines it. A row whose Card column says *ground* is a declared primitive: notation the pool uses without a definition card, because defining it is somebody else's job.

This file is **normative**: one name and one symbol per concept, pool-wide. Graduating a card means translating its source's lettering into the cast below exactly as it translates the source's terminology; a card's Notes may record what the source called things.

**Written by hand.** Nothing generates this table. `tools/notation_lint.py` checks it both ways: every symbol a Statement uses appears here, and every row naming a card names a card whose Statement really contains that symbol.

## The cast — role letters

Recurring roles get fixed letters, so that a reader who has seen one card can read the next. A letter is listed here and not in the tables below when it is a role rather than a defined object — what it stands for changes from card to card, but its part does not.

| Letter | Role |
|---|---|
| $n$ | the size of the matrices, $n \ge 2$; the vertex set is $[n]$ |
| $Q$ | an orthogonal upper Hessenberg matrix; $Q'$ a second one |
| $A$ | the adjacency matrix of a support digraph — a $0/1$ matrix, never a matrix of values |
| $S$ | an active set, $S \subseteq [n-1]$; $S'$ a second one; $m = \lvert S \rvert$; elements $s_1 < \cdots < s_m$ |
| $t$ | the single element of a singleton active set $\{t\}$ |
| $\theta$ | an angle vector $(\theta_0, \dots, \theta_{n-2})$; $\theta_k$ one of its entries |
| $i$, $j$ | a row and a column index — equivalently the tail and the head of an arc |
| $k$ | an index of the angle vector, $0 \le k \le n-2$; also the position of a cut |
| $v$ | a vertex, when it is not being read as a row or a column |
| $\varphi$, $\Phi$ | a digraph isomorphism |
| $\rho$ | the rotation $\rho(i) = i-1$, $\rho(1) = n$, one step along the spine |

## The matrix side

| Notation | Meaning | Card |
|---|---|---|
| $[n]$ | $\{1, 2, \dots, n\}$ — the index set, and the vertex set | *ground* |
| $\mathbb{R}^{n \times n}$ | the real $n \times n$ matrices | *ground* |
| $Q^\top$ | the transpose | *ground* |
| $I$ | the identity matrix | *ground* |
| $Q_{ij}$ | the entry of $Q$ in row $i$, column $j$ | *ground* |
| $\mathcal{H}_n$ | the orthogonal upper Hessenberg matrices in $\mathbb{R}^{n \times n}$ | [[def-orthogonal-upper-hessenberg]] |
| $\simeq_{\mathrm{sign}}$ | sign-equivalence of matrices | [[def-sign-equivalence]] |
| $D_L$, $D_R$ | the left and right signature matrices of a sign-equivalence | [[def-sign-equivalence]] |
| $G_k(\theta)$ | the Givens rotation in the plane of coordinates $k$, $k{+}1$ | [[def-givens-rotation]] |
| $Q_n(\theta)$ | the ordered Givens product $G_0(\theta_0) \cdots G_{n-2}(\theta_{n-2})$ | [[def-givens-rotation]] |
| $\Theta_n$ | the unreduced angle vectors | [[def-unreduced-angle-vector]] |

## The combinatorial side

| Notation | Meaning | Card |
|---|---|---|
| $i \to j$ | an arc from $i$ to $j$; a loop when $i = j$ | *ground* |
| $\cong$ | isomorphism of digraphs | *ground* |
| $D(Q)$ | the support digraph of a matrix | [[def-support-digraph]] |
| $S(\theta)$ | the active set of an angle vector | [[def-active-set]] |
| $R(S)$, $C(S)$ | the active rows and the active columns of $S$ | [[def-active-set]] |
| $D_n(S)$ | the combinatorial digraph of the active set $S$ | [[def-active-set]] |
| $D_{n,t}$ | shorthand for $D_n(\{t\})$ | [[lem-singleton-isomorphism]] |
| $H$ | the spine: the directed Hamilton cycle $1 \to n \to \cdots \to 2 \to 1$ | [[lem-unique-hamilton-cycle]] |
| $d^{+}$, $d^{-}$ | out-degree, in-degree | [[prop-degree-formulas]] |

## Counting

| Notation | Meaning | Card |
|---|---|---|
| $\lfloor \cdot \rfloor$, $\lceil \cdot \rceil$ | floor and ceiling | *ground* |
| $F_k$ | the $k$-th Fibonacci number, $F_0 = 0$, $F_1 = 1$, $F_{m+2} = F_{m+1} + F_m$ | *ground* |
| $N_n$ | the number of isomorphism classes of connected support digraphs | [[thm-enumeration]] |
| $N_n^{\mathrm{loopless}}$ | the same count, loopless digraphs only | [[thm-loopless-enumeration]] |

## Ground notions

Notions the pool uses without a definition card. Anything used but neither carded nor listed here is an undeclared debt (`rules.md` § 4).

- **Directed-graph vocabulary** — digraph, arc, loop, in- and out-degree, isomorphism of digraphs, directed Hamilton cycle, directed cut, weak connectedness.
- **Linear algebra** — matrix, entry, transpose, identity, diagonal matrix, matrix product, orthogonality.
- **Arithmetic** — floor, ceiling, binomial coefficients, the Fibonacci numbers.
- **Trigonometry** — $\sin$, $\cos$, $\pi$.

## Conventions

- **Arcs are written $i \to j$ and mean $Q_{ij} \ne 0$** — row to column. The transpose convention is never used.
- **Indices differ by one on purpose.** Vertices and matrix indices run over $[n] = \{1, \dots, n\}$; the angle vector runs over $k = 0, \dots, n-2$. That shift is what makes $S(\theta) = \{k+1 : \cos\theta_k \ne 0\}$ land in $[n-1]$. Both conventions are kept rather than renumbering one of them, because the matrix side and the combinatorial side are stated independently and meet only at [[thm-bridge]].
- **$R$ and $C$ are written without their argument** once an active set $S$ is fixed in a statement.
- **"Rows and columns" is ambiguous and both readings are in use.** Plain rows and columns of a matrix are ordinary linear algebra; *active* rows and columns are $R(S)$ and $C(S)$. Only the second is ever linked.
- **$m$ always means $\lvert S \rvert$**, never a second matrix size.
