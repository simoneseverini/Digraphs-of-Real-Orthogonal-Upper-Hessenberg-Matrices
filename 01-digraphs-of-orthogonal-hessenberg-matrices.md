---
topic: hessenberg-digraphs
type: topic
section: "01"
date: 2026-08-02
tags: [linear-algebra, digraphs, hessenberg]
---
# Digraphs of real-orthogonal upper Hessenberg matrices

Which directed graphs arise as the zero / non-zero pattern of an orthogonal upper Hessenberg matrix — and why the answer is a subset of $\{1, \dots, n-1\}$.

Take an $n \times n$ real matrix, forget the values of its entries, and keep only which of them are non-zero. What is left is a directed graph on $n$ vertices. For most classes of matrices this loses everything interesting. For orthogonal upper Hessenberg matrices it loses almost nothing: the graph determines the matrix up to signs, and the graphs that occur can be listed.

## The two conditions

Upper Hessenberg is a sparsity condition and orthogonality is a rigidity condition. Separately, neither says much.

![[def-orthogonal-upper-hessenberg]]

The object being classified is what survives forgetting the values:

![[def-support-digraph]]

![[fig-support-digraph-example.svg]]

*A $4 \times 4$ upper Hessenberg matrix ($\bullet$ = nonzero) and its support digraph. Each nonzero entry $Q_{ij}$ becomes a directed arc $i \to j$.*

Signs are invisible to it, which is what lets the classification normalise them away without loss:

![[def-sign-equivalence]]

![[cor-sign-invariance-of-support-digraph]]

## Rotations, and the set they leave behind

Together the two conditions force a factorization. An orthogonal upper Hessenberg matrix is a product of plane rotations, one for each adjacent pair of coordinates, taken in order.

![[def-givens-rotation]]

![[def-unreduced-angle-vector]]

The unreduced hypothesis is not a technicality. A vanishing subdiagonal entry splits the matrix into two independent blocks, and the digraph falls apart with it; every theorem below assumes it away.

![[thm-universality]]

So the matrices are parametrised by angle vectors. But the support digraph cannot see an angle — only whether its cosine vanishes. That single bit per angle is the whole content:

![[def-active-set]]

## The bridge

Everything so far has two sides that have not yet been connected: matrices with their supports, and the purely combinatorial $D_n(S)$ built from a subset alone. This is the statement that identifies them, and after it the subject is combinatorics.

![[thm-bridge]]

![[ex-d6-s24]]

![[fig-d6-s24-anatomy.svg]]

*Anatomy of $D_6(\{2,4\})$. Solid arrows form the spine. Dashed blue arrows are the overlay arcs from active rows $R = \{1,3,5\}$ to active columns $C = \{2,4,6\}$. Self-loops occur exactly at vertices of $R \cap C$; here that intersection is empty.*

The same example on the matrix side shows what the bridge predicts entry by entry — the spine entries on the subdiagonal, and the overlay entries exactly at the intersections of active rows with active columns:

![[fig-q6-s24-support-pattern.svg]]

*Support pattern of $Q_6(\{2,4\})$. The thick boundary marks the upper Hessenberg band; open circles are the mandatory subdiagonal spine entries; solid dots are overlay nonzeros at the intersections (purple) of active rows (blue) and active columns (red).*

![[ex-d5-s2]]

![[fig-d5-s2.svg]]

*The loopless support digraph $D_5(\{2\})$. Active rows $R = \{1,3\}$ (blue fill) and active columns $C = \{2,5\}$ (red outline) are disjoint.*

## Recovering the set from the graph

The bridge says every $D_n(S)$ occurs. It does not say that different sets give different graphs — and up to isomorphism, a graph has no labels to read $S$ off. That the labels can be recovered anyway is proved in the next chapter; the statement is:

![[thm-rigidity]]

![[ex-d5-s13]]

![[fig-d5-s13.svg]]

*The support digraph $D_5(\{1,3\})$. Since $R \cap C = \{1\}$, there is exactly one self-loop, at vertex $1$.*

## The classification

![[thm-classification]]

The three clauses are independent statements and the classification is their packaging: realizability says the map $S \mapsto D_n(S)$ is onto, the bridge says it computes matrix supports, and rigidity says it is injective where it can be. What remains is to see why rigidity holds, where it fails, and what the resulting count is — which is [[02-isomorphism-classes-and-enumeration|the next chapter]].
