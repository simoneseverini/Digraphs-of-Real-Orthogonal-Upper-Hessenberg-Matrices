import VersoManual
import Paper.Tikz
import HessenbergDigraphs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Paper
open HessenbergDigraphs Matrix

#doc (Manual) "Setup and definitions" =>

We work with $`n \times n` real matrices ($`n \ge 2`), indexed by
$`[n] = \{1, 2, \dots, n\}` throughout the paper.

*Definition 2.1 (orthogonal upper Hessenberg matrix).* {name}`OrthogonalHessenberg` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/Matrix/OrthogonalHessenberg.lean#L66)

A matrix $`Q \in \mathbb{R}^{n \times n}` is _upper Hessenberg_ if
$`Q_{ij} = 0` whenever $`j + 1 < i`, and _orthogonal_ if
$`Q^\top Q = I`. We write $`\mathcal{H}_n` for the set of orthogonal
upper Hessenberg matrices in $`\mathbb{R}^{n \times n}`.

{docstring OrthogonalHessenberg (hideFields := true)}

*Definition 2.2 (support digraph).* {name}`OrthogonalHessenberg.supportDigraph` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/Matrix/OrthogonalHessenberg.lean#L121)

The _support digraph_ of $`Q`, denoted $`D(Q)`, is the directed graph
on $`[n]` with an arc $`i \to j` whenever $`Q_{ij} \ne 0`.

{docstring OrthogonalHessenberg.supportDigraph}

```tikz
\begin{tikzpicture}[
  v/.style={circle, draw=black, line width=0.6pt, inner sep=1.2pt,
            minimum size=18pt, font=\small},
  arr/.style={-{Stealth[length=5pt]}, line width=0.8pt, draw=black},
]
\node (mat) at (-2.5, 0) {$Q = \begin{pmatrix}
\bullet & \bullet & 0 & \bullet \\
\bullet & \bullet & 0 & \bullet \\
0 & \bullet & 0 & 0 \\
0 & 0 & \bullet & 0
\end{pmatrix}$};

\draw[-{Stealth[length=5pt]}, thick] (0.6, 0) -- (1.8, 0)
  node[midway, above, font=\footnotesize] {$D(Q)$};

\node[v] (1) at (3.0, 1.0)  {1};
\node[v] (2) at (5.0, 1.0)  {2};
\node[v] (3) at (5.0, -1.0) {3};
\node[v] (4) at (3.0, -1.0) {4};

\draw[arr, loop above, looseness=8, min distance=8mm] (1) to (1);
\draw[arr, loop above, looseness=8, min distance=8mm] (2) to (2);
\draw[arr, bend left=12] (1) to (2);
\draw[arr, bend left=12] (2) to (1);
\draw[arr] (1) to (4);
\draw[arr] (2) to (4);
\draw[arr] (3) to (2);
\draw[arr] (4) to (3);
\end{tikzpicture}
```

_Figure 2.1 — a 4 × 4 upper Hessenberg matrix and its support digraph_ $`D(Q)`. _Each nonzero entry $`Q_{ij}` becomes a directed arc $`i \to j`._

*Definition 2.3 (sign-equivalence).* {name}`Matrix.SignEquiv` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/Matrix/SignEquivalence.lean#L62)

Two matrices $`Q, Q' \in \mathbb{R}^{n \times n}` are _sign-equivalent_,
written $`Q \simeq_{\mathrm{sign}} Q'`, if $`Q' = D_L\, Q\, D_R` for some
diagonal matrices $`D_L, D_R` with entries in $`\{\pm 1\}`. Sign-equivalent
matrices have identical zero / non-zero patterns, so $`D(Q) = D(Q')`.

{docstring Matrix.SignEquiv}

*Definition 2.4 (Givens rotation, ordered Givens product).* {name}`Matrix.givensRotation` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/Matrix/Givens/Basic.lean#L69), {name}`Matrix.givensProduct` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/Matrix/Givens/Product.lean#L70)

For $`k \in \{0, \dots, n-2\}` and $`\theta \in \mathbb{R}`, the
_Givens rotation_ $`G_k(\theta) \in \mathbb{R}^{n \times n}` is the
identity with the $`2 \times 2` block at rows / columns $`(k, k{+}1)`
replaced by
$`\begin{bmatrix} \cos\theta & -\sin\theta \\ \sin\theta & \cos\theta \end{bmatrix}`.
The _ordered Givens product_ of an angle vector
$`\theta = (\theta_0, \dots, \theta_{n-2})` is
$$`Q_n(\theta) \;\coloneqq\; G_0(\theta_0)\, G_1(\theta_1)\,\cdots\,G_{n-2}(\theta_{n-2}).`
The product $`Q_n(\theta)` is always orthogonal upper Hessenberg, and
its $`(k{+}1, k)` subdiagonal entry equals $`\sin\theta_k`.

{docstring Matrix.givensRotation}

{docstring Matrix.givensProduct}

The angle vector is called _unreduced_ if every $`\sin\theta_k` is
non-zero; equivalently, every subdiagonal entry of $`Q_n(\theta)` is
non-zero. We write $`\Theta_n` for the set of such unreduced angle
vectors.

*Definition 2.5 (active set, combinatorial digraph).* {name}`ActiveSet` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/ActiveSet.lean#L69), {name}`Arc` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/Combinatorial/Arc.lean#L61)

For $`\theta \in \Theta_n`, the _active set_ is
$$`S(\theta) \;\coloneqq\; \bigl\{\, k \in [n-1] \,:\, \cos\theta_{k-1} \ne 0\,\bigr\} \;\subseteq\; [n-1].`
On the combinatorial side, fix any subset $`S \subseteq [n-1]`. From
$`S` we derive
$$`R(S) \;\coloneqq\; \{1\} \cup \{k+1 : k \in S\}, \qquad C(S) \;\coloneqq\; S \cup \{n\}`
(active rows / active columns), and the digraph $`D_n(S)` on $`[n]` has
arcs of two kinds: _spine_ arcs $`j+1 \to j` for $`1 \le j \le n-1`,
and _overlay_ arcs $`i \to j` whenever $`i \in R(S)`, $`j \in C(S)`,
and $`i \le j`.

{docstring ActiveSet (hideFields := true)}

{docstring Arc (allowMissing := true)}

*Example 2.6 ($`n = 6`, $`S = \{2, 4\}` — anatomy of $`D_6(\{2,4\})`).* {name}`example_D6_S24` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/PaperExamples.lean#L65)

The angle vector $`\theta = (\pi/2, \pi/4, \pi/2, \pi/4, \pi/2)`
produces $`\cos\theta_k \ne 0` exactly for $`k \in \{1, 3\}`, hence
$`S = \{2, 4\}`. The active rows and columns are
$$`R = \{1, 3, 5\}, \qquad C = \{2, 4, 6\},`
and the resulting digraph $`D_6(\{2, 4\})` consists of the spine cycle
together with overlay arcs from $`R` to $`C`, and a unique self-loop
at vertex $`5` (the only element of $`R \cap C`).

{docstring example_D6_S24}

```tikz
\begin{tikzpicture}[
  v/.style={circle, draw=black, line width=0.6pt, inner sep=1.2pt,
            minimum size=18pt, font=\small},
  spine/.style={->, line width=1.0pt, draw=black!60},
  over/.style={->, line width=0.9pt, draw=blue!70!black, densely dashed},
  Rnode/.style={fill=blue!10},
  Cnode/.style={draw=red!80!black, line width=1.2pt},
  RCnode/.style={fill=blue!10, draw=red!80!black, line width=1.2pt}
]
\def\radius{2.3}
\node[v,Rnode]  (1) at (90:\radius)  {1};
\node[v]        (6) at (30:\radius)  {6};
\node[v,RCnode] (5) at (-30:\radius) {5};
\node[v,Cnode]  (4) at (-90:\radius) {4};
\node[v,Rnode]  (3) at (-150:\radius){3};
\node[v,Cnode]  (2) at (150:\radius) {2};

\draw[spine] (1) -- (6);
\draw[spine] (6) -- (5);
\draw[spine] (5) -- (4);
\draw[spine] (4) -- (3);
\draw[spine] (3) -- (2);
\draw[spine] (2) -- (1);

\draw[over, bend left=14] (1) to (2);
\draw[over, bend left=14] (1) to (4);
\draw[over] (1) to (6);
\draw[over, bend left=14] (3) to (4);
\draw[over, bend left=14] (3) to (6);
\draw[over, loop right] (5) to (5);
\draw[over, bend left=14] (5) to (6);
\end{tikzpicture}
```

_Figure 2.2 — anatomy of $`D_6(\{2,4\})`, with $`R = \{1,3,5\}` and $`C = \{2,4,6\}`. Solid grey arrows are the directed Hamilton cycle (spine); dashed blue arrows are overlay arcs from active rows (blue fill) to active columns (red outline). The self-loop at vertex 5 arises because $`5 \in R \cap C`._
