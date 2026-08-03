---
id: 116ee5d2f614
type: definition
lean:
  - decl: HessenbergDigraphs.OrthogonalHessenberg.supportDigraph
    module: HessenbergDigraphs.Matrix.OrthogonalHessenberg
    line: 122
    state: proven
---

# Definition — support digraph

The translation from linear algebra to combinatorics: forget the values of the entries and keep only which ones are non-zero. Everything this network proves is a statement about the digraph that survives.

## Statement

> [!definition] Support digraph
> The *support digraph* of an $n \times n$ real matrix $Q$, denoted $D(Q)$, is the directed graph on $[n]$ with an arc $i \to j$ whenever $Q_{ij} \ne 0$.

## Notes

> [!note]- Notes (click to expand)
> - Loops are allowed and carry information: $i \to i$ records a non-zero diagonal entry. Which vertices carry one is settled by [[lem-loops-in-model]].
> - ![[fig-support-digraph-example.svg]]
