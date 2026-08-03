---
topic: hessenberg-digraphs
type: topic
section: "02"
date: 2026-08-02
tags: [digraphs, enumeration, rigidity]
---
# Isomorphism classes and enumeration

Why an active set of size at least two is recoverable from its digraph, why singletons are the one exception, and what the two facts count to.

The classification of [[01-digraphs-of-orthogonal-hessenberg-matrices|the previous chapter]] produces a digraph $D_n(S)$ for every $S \subseteq [n-1]$. Whether that map is injective is a different question, and a harder one: an isomorphism may permute the vertices however it likes, so nothing labelled survives it a priori. The answer is that it is injective wherever it can be — $2^{n-1}$ sets give $2^{n-1}$ classes, minus exactly the singleton coincidences.

## Almost acyclic

Everything follows from one asymmetry. Overlay arcs run from a smaller index to a larger one, spine arcs run one step the other way, and so at every cut of the vertex set into a low half and a high half, exactly one arc goes backwards.

![[lem-cut]]

That one arc is forced, and the forcing propagates: a cycle visiting every vertex has to use all $n-1$ of them.

![[lem-unique-hamilton-cycle]]

This is the fact that makes the labelling recoverable. An isomorphism carries Hamilton cycles to Hamilton cycles; there is only one of them on each side; so an isomorphism is a rotation along the spine, and a rotation is determined by where it sends a single vertex.

## Reading the set off the degrees

Which rotation is settled by counting arcs at each vertex. The in-degrees on the active columns are $2, 3, \dots, m+1$ in increasing order of the elements of $S$, and everything else has in-degree $1$ — so the degree sequence recovers $S$ as an ordered set.

![[prop-degree-formulas]]

![[thm-rigidity]]

The hypothesis $|S| \ge 2$ is where the argument is used, not where it is convenient: with $m \ge 2$ there is a vertex of in-degree exactly $m$ and it is unique, which is the fixed point the rotation is pinned to. With $m = 1$ there is no such vertex, and indeed the conclusion is false.

## The one exception

A singleton gives the spine with two chords, and rotating the spine slides one chord onto the other.

![[lem-singleton-isomorphism]]

So $\{t\}$ and $\{n-t\}$ collide and nothing else does. The pairing is a fixed point when $t = n - t$, which is why the number of singleton classes is $\lceil (n-1)/2 \rceil$ rather than half of $n-1$.

## The count

![[thm-enumeration]]

The floor function is the whole content of the collapse: $2^{n-1}$ labelled configurations, minus the $\lfloor (n-1)/2 \rfloor$ that the singleton rotation identifies in pairs. Restricting to digraphs without loops replaces the power of two by a Fibonacci number — that is [[03-loopless-digraphs-and-examples|the next chapter]].
