import VersoManual
import Paper.Tikz
import HessenbergDigraphs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Paper
open HessenbergDigraphs

#doc (Manual) "Main theorems" =>

The classification of support digraphs of unreduced real orthogonal
upper Hessenberg matrices is the conjunction of four formal statements:
a universality result on the matrix side, a bridge that identifies the
matrix support with the combinatorial digraph, and two structural facts
on the combinatorial side (rigidity, enumeration).

*Theorem 2.7 (universality).* {name}`OrthogonalHessenberg.exists_givensFactorization` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/Matrix/Givens/Factorization.lean#L854)

Every unreduced $`Q \in \mathcal{H}_n` is sign-equivalent to a canonical
Givens product: there exists $`\theta \in \Theta_n` with
$`Q \simeq_{\mathrm{sign}} Q_n(\theta)`.

{docstring OrthogonalHessenberg.exists_givensFactorization}

*Proof sketch.*
Induction on $`n`. Right-multiply $`Q` by the transpose of a Givens
factor chosen to clear the last row to $`e_n^\top`; orthogonality
forces the last column to $`e_n` as well, so the principal
$`(n{-}1) \times (n{-}1)` corner is itself orthogonal upper Hessenberg,
and the induction hypothesis applies. The accumulated sign discrepancies
along the inductive peel-off are absorbed into the diagonal $`D_L, D_R`
of the sign-equivalence relation.

*Theorem 2.8 (bridge).* {name}`digraph_model` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/Realization/DigraphModel.lean#L150)

For every $`\theta \in \Theta_n`, the matrix support agrees with the
combinatorial digraph:
$$`D\bigl(Q_n(\theta)\bigr) \;=\; D_n\bigl(S(\theta)\bigr).`

{docstring digraph_model}

*Proof sketch.*
Two inclusions, both stated entry-wise on $`Q_n(\theta)_{ij}`. The
subdiagonal entries are $`\sin\theta_{j} \ne 0` by the unreduced
hypothesis, exhibiting all spine arcs. For an upper-triangular entry
$`i \le j`, a row / column-vanishing analysis on the Givens product
shows that $`Q_n(\theta)_{ij} \ne 0` iff $`\cos\theta_{i-1} \ne 0` and
$`\cos\theta_{j} \ne 0`, which by definition of $`S(\theta)` is exactly
the overlay condition $`i \in R(S(\theta))`, $`j \in C(S(\theta))`.

The bridge can be read off concretely from the matrix support pattern.
Returning to the running example $`S = \{2, 4\}` of Example 2.6, the
two kinds of nonzero entries promised by the theorem are the spine
entries $`(j+1, j)` on the subdiagonal, and the overlay entries at
positions $`(i, j)` with $`i \in R`, $`j \in C`, $`i \le j`.

```tikz
\begin{tikzpicture}[
    scale=0.9,
    grid line/.style={draw=gray!20, line width=0.5pt},
    hessenberg line/.style={draw=black, line width=2pt, line cap=round, line join=round},
    row band/.style={fill=blue!5},
    col band/.style={fill=red!5},
    cross cell/.style={fill=violet!15},
    subdiag node/.style={circle, draw=black, thick, inner sep=0pt, minimum size=5pt},
    entry node/.style={circle, fill=black, inner sep=0pt, minimum size=5pt}
]
\def\nN{6}
\def\Rlist{1,3,5}
\def\Clist{2,4,6}

\foreach \r in \Rlist {
    \fill[row band] (0.5, -\r+0.5) rectangle (\nN.5, -\r-0.5);
    \node[anchor=east, blue!80!black, font=\footnotesize] at (-0.4, -\r) {$i \in R$};
}
\foreach \c in \Clist {
    \fill[col band] (\c-0.5, -0.5) rectangle (\c+0.5, -\nN.5);
    \node[anchor=south, red!80!black, font=\footnotesize] at (\c, 0.6) {$j \in C$};
}

\foreach \r in \Rlist {
    \foreach \c in \Clist {
        \fill[cross cell] (\c-0.5, -\r+0.5) rectangle (\c+0.5, -\r-0.5);
    }
}

\foreach \k in {1,...,\nN} {
    \node[font=\sffamily\footnotesize] at (0, -\k) {\k};
    \node[font=\sffamily\footnotesize] at (\k, 0.2) {\k};
}

\draw[grid line] (0.5, -0.5) grid (\nN.5, -\nN.5);
\draw[black, thin] (0.5, -0.5) rectangle (\nN.5, -\nN.5);

\draw[hessenberg line]
    (0.5, -2.5)
    \foreach \k in {1,...,4} {
        -- (\k.5, -\k.5-1)
        -- (\k.5, -\k.5-2)
    }
    -- (6.5, -6.5);

\foreach \k in {1,...,5} {
    \node[subdiag node] at (\k, -\k-1) {};
}
\foreach \r in \Rlist {
    \foreach \c in \Clist {
        \pgfmathparse{int(\r<=\c)}
        \ifnum\pgfmathresult=1
            \node[entry node] at (\c, -\r) {};
        \fi
    }
}
\end{tikzpicture}
```

_Figure 2.3 — support pattern of $`Q_6(\{2, 4\})`, the matrix-side counterpart of Figure 2.2. The thick boundary marks the upper Hessenberg band; open circles are the mandatory subdiagonal spine entries; solid dots are overlay nonzeros at the intersections (purple) of active rows (blue) and active columns (red). The Bridge theorem says these are exactly the nonzero entries of any unreduced $`Q_n(\theta)` with $`S(\theta) = \{2, 4\}`._

*Example 2.9 ($`n = 5`, $`S = \{2\}`).* {name}`example_D5_S2` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/PaperExamples.lean#L125)

The angle vector $`\theta = (\pi/2, \pi/4, \pi/2, \pi/2)` gives
$$`Q = \begin{pmatrix}
0 & \tfrac{1}{\sqrt{2}} & 0 & 0 & \tfrac{1}{\sqrt{2}} \\
-1 & 0 & 0 & 0 & 0 \\
0 & -\tfrac{1}{\sqrt{2}} & 0 & 0 & \tfrac{1}{\sqrt{2}} \\
0 & 0 & -1 & 0 & 0 \\
0 & 0 & 0 & -1 & 0
\end{pmatrix}, \qquad
A = \begin{pmatrix}
0 & 1 & 0 & 0 & 1 \\
1 & 0 & 0 & 0 & 0 \\
0 & 1 & 0 & 0 & 1 \\
0 & 0 & 1 & 0 & 0 \\
0 & 0 & 0 & 1 & 0
\end{pmatrix}.`
The Hamilton cycle is $`1 \to 5 \to 4 \to 3 \to 2 \to 1`. Since
$`R = \{1, 3\}` and $`C = \{2, 5\}` are disjoint, the digraph is
loopless; $`A` is exactly the support pattern predicted by Theorem 2.8.

{docstring example_D5_S2}

```tikz
\begin{tikzpicture}[
  v/.style={circle, draw=black, line width=0.6pt, inner sep=1.2pt,
            minimum size=18pt, font=\small},
  cyc/.style={->, line width=1.0pt, draw=black},
  extra/.style={->, line width=0.9pt, draw=black},
  Rnode/.style={fill=blue!10},
  Cnode/.style={draw=red!80!black, line width=1.2pt}
]
\node[v,Rnode] (1) at ( 90:2.1) {1};
\node[v,Cnode] (5) at ( 18:2.1) {5};
\node[v]       (4) at (-54:2.1) {4};
\node[v,Rnode] (3) at (-126:2.1) {3};
\node[v,Cnode] (2) at (162:2.1) {2};

\draw[cyc] (1) -- (5);
\draw[cyc] (5) -- (4);
\draw[cyc] (4) -- (3);
\draw[cyc] (3) -- (2);
\draw[cyc] (2) -- (1);

\draw[extra, bend left=12] (1) to (2);
\draw[extra, bend left=12] (3) to (5);
\end{tikzpicture}
```

_Figure 2.4 — the loopless support digraph $`D_5(\{2\})`. Active rows $`R = \{1,3\}` (blue fill) and active columns $`C = \{2,5\}` (red outline) are disjoint._

*Theorem 2.10 (rigidity).* {name}`rigid` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/Combinatorial/Rigidity.lean#L329)

Let $`S, S' \subseteq [n-1]` with $`|S|, |S'| \ge 2`. If
$`D_n(S) \cong D_n(S')` as digraphs, then $`S = S'`.

{docstring rigid}

*Proof sketch.*
The key combinatorial fact is the _cut lemma_: in $`D_n(S)`, the only
arc from $`\{k{+}1, \dots, n\}` to $`\{1, \dots, k\}` is the spine arc
$`k{+}1 \to k`. This forces every isomorphism to fix the unique
directed Hamilton cycle $`1 \to n \to n{-}1 \to \cdots \to 2 \to 1`.
A pigeonhole argument on the cut, combined with degree analysis at the
maximum-in-degree vertex (which is $`n` when $`|S| \ge 2`), forces the
isomorphism to fix $`n`, after which a downward induction along the
cycle forces the identity. The case $`|S| = 1` is the only failure:
the cyclic rotation $`\rho^t` exhibits $`D_n(\{t\}) \cong D_n(\{n - t\})`,
with no further coincidences.

*Example 2.11 ($`n = 5`, $`S = \{1, 3\}`).* {name}`example_D5_S13` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/PaperExamples.lean#L176)

A two-element example illustrating Theorem 2.10: any $`D_5(S')`
isomorphic to $`D_5(\{1,3\})` must have $`S' = \{1, 3\}`. The angle
vector $`\theta = (\pi/4, \pi/2, \pi/4, \pi/2)` gives
$$`Q = \begin{pmatrix}
\tfrac{1}{\sqrt{2}} & 0 & \tfrac{1}{2} & 0 & \tfrac{1}{2} \\
-\tfrac{1}{\sqrt{2}} & 0 & \tfrac{1}{2} & 0 & \tfrac{1}{2} \\
0 & -1 & 0 & 0 & 0 \\
0 & 0 & -\tfrac{1}{\sqrt{2}} & 0 & \tfrac{1}{\sqrt{2}} \\
0 & 0 & 0 & -1 & 0
\end{pmatrix}, \qquad
A = \begin{pmatrix}
1 & 0 & 1 & 0 & 1 \\
1 & 0 & 1 & 0 & 1 \\
0 & 1 & 0 & 0 & 0 \\
0 & 0 & 1 & 0 & 1 \\
0 & 0 & 0 & 1 & 0
\end{pmatrix}.`
Here $`R \cap C = \{1\}`, so there is exactly one self-loop at vertex
$`1`.

{docstring example_D5_S13}

```tikz
\begin{tikzpicture}[
  v/.style={circle, draw=black, line width=0.6pt, inner sep=1.2pt,
            minimum size=18pt, font=\small},
  cyc/.style={->, line width=1.0pt, draw=black},
  extra/.style={->, line width=0.9pt, draw=black},
  Rnode/.style={fill=blue!10},
  Cnode/.style={draw=red!80!black, line width=1.2pt},
  RCnode/.style={fill=blue!10, draw=red!80!black, line width=1.2pt}
]
\node[v,RCnode] (1) at ( 90:2.1) {1};
\node[v,Cnode]  (5) at ( 18:2.1) {5};
\node[v,Rnode]  (4) at (-54:2.1) {4};
\node[v,Cnode]  (3) at (-126:2.1) {3};
\node[v,Rnode]  (2) at (162:2.1) {2};

\draw[cyc] (1) -- (5);
\draw[cyc] (5) -- (4);
\draw[cyc] (4) -- (3);
\draw[cyc] (3) -- (2);
\draw[cyc] (2) -- (1);

\draw[extra, loop above] (1) to (1);
\draw[extra, bend left=14] (1) to (3);
\draw[extra, bend left=10] (2) to (3);
\draw[extra, bend left=14] (2) to (5);
\draw[extra, bend left=10] (4) to (5);
\end{tikzpicture}
```

_Figure 2.5 — the support digraph $`D_5(\{1,3\})`. Since $`R \cap C = \{1\}`, there is exactly one self-loop at vertex 1._

*Theorem 2.12 (classification).* {name}`classification` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/Classification.lean#L53)

Fix $`n \ge 2`. The classification of support digraphs of unreduced
orthogonal upper Hessenberg matrices is the conjunction:

1. _(realizability)_ every $`S \subseteq [n-1]` is of the form
   $`S(\theta)` for some $`\theta \in \Theta_n`;
2. _(bridge)_ for every $`\theta`, the support of $`Q_n(\theta)` equals
   $`D_n(S(\theta))`;
3. _(rigidity)_ for every $`S, S'` with $`|S|, |S'| \ge 2`,
   $`D_n(S) \cong D_n(S') \Rightarrow S = S'`.

{docstring classification}

The classification declaration is a one-line term-level packaging of
three independently-proved components; it adds no mathematical content
and exists only so the paper has a single Lean handle to cite.
Realizability is witnessed by the explicit angle choice
$`\theta_k = \pi/4` if $`k+1 \in S`, $`\theta_k = \pi/2` otherwise;
this gives $`\sin \theta_k \ne 0` always and $`\cos\theta_k \ne 0`
exactly on $`S`.
