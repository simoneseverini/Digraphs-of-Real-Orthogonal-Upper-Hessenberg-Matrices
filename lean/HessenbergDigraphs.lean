/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Classification
import HessenbergDigraphs.Combinatorial.Loop
import HessenbergDigraphs.Combinatorial.Hamilton
import HessenbergDigraphs.Combinatorial.Singleton.Iso
import HessenbergDigraphs.Combinatorial.Enumeration
import HessenbergDigraphs.Combinatorial.ClassCount
import HessenbergDigraphs.RealizableCount
import HessenbergDigraphs.PaperExamples
import HessenbergDigraphs.Matrix.SignEquivalence
import HessenbergDigraphs.Matrix.Givens.Factorization
import HessenbergDigraphs.Matrix.Orthogonal

/-!
# `HessenbergDigraphs` library facade

Top-level entry point for the `HessenbergDigraphs` library, the Lean 4
formalization of the classification of support digraphs of real
orthogonal upper Hessenberg matrices, accompanying the paper
"Automation of routine mathematics: a case study" (Li, Severini),
based on Severini, "Digraphs of Real Orthogonal Upper Hessenberg
Matrices".

## Architecture

The library is organized into three strictly separated tiers plus
a small set of cross-tier paper-side primitives at the top level:

* **Cross-tier primitives** — `HessenbergDigraphs.Vertex` and
  `HessenbergDigraphs.ActiveSet` at the top level. `Vertex n` is the
  paper-side vertex type; `ActiveSet n` carries `activeRows` /
  `activeCols` / `digraph` / `NoConsecutive`. Imported by every tier.
* **Tier 1 — `HessenbergDigraphs.Combinatorial.*`** — pure combinatorial
  theory of `D_n(S)`. The `Arc` inductive (with `Loop`), the abstract
  `Digraph`, plus loops, Hamilton cycle, degrees, cut lemma,
  rigidity, singleton coincidence, enumeration.
* **Tier 2 — `HessenbergDigraphs.Matrix.*`** — pure matrix theory.
  `OrthogonalHessenberg`, `UnreducedAngles`, Hessenberg / unreduced
  predicates, Givens rotations, sign equivalence, subdiagonal
  entries, connectivity break.
* **Tier 3 — `HessenbergDigraphs.Realization.*`** — matrix → digraph
  realization layer. `activeSet`, vanishing rows / cols, propagation,
  the bridge theorem `digraph_model` and realizability `completeness`.
* `HessenbergDigraphs.Classification` — the apex theorem assembling
  all three layers.

The bundled paper-side objects listed above are distributed by
domain across the tiers, not collected in any single folder or
namespace.

The combinatorial and matrix tiers are independent: neither imports
the other directly. They meet only in the bridge tier.

## Main results

* `classification` — apex classification theorem (Paper: Theorem 1).
* `digraph_model` — bridge from `givensProduct θ` to `D_n(activeSet θ)`
  (Paper: Theorem 7).
* `completeness` — every valid `S` is realized by some unreduced `θ`
  (Paper: Theorem 4).
* `rigid` — automorphism rigidity for `|S| ≥ 2` (Paper: Theorem 10).
* `singleton_iso`, `singleton_iso_unique` — singleton-set isomorphism
  characterization (Paper: Lemma 11).
* `loopless_iff` — loopless characterization (Paper: Corollary 14).
* `count_formula` — connected-class count
  `2^(n - 1) - ⌊(n - 1) / 2⌋` (Paper: Theorem 12).
* `card_isoClasses_quot` — the same count as a genuine cardinality:
  `Nat.card (Quotient (isoSetoid n)) = 2^(n - 1) - ⌊(n - 1) / 2⌋`, i.e. the
  active sets modulo digraph isomorphism number exactly that many. Backed by
  the complete invariant `isoInvariant_eq_iff` and `card_isoClasses`
  (Paper: Theorem 12).
* `count_loopless_formula` — loopless connected-class count
  `Nat.fib (n - 1) - ⌊(n - 3) / 2⌋` (Paper: Theorem 15).
* `card_looplessClasses_quot` — the loopless count as a genuine cardinality:
  `Nat.card (Quotient (looplessIsoSetoid n)) = Nat.fib (n - 1) - ⌊(n - 3) / 2⌋`
  (Paper: Theorem 15).
* `realizable_classCount` — certificate tying the executable calculator to the
  Givens-product supports: those are exactly `{ D_n(S) : S }`, and up to
  isomorphism number the calculator's `countClasses n`. Routes through
  `digraph_model`, `completeness`, and `rigid`.
* `matrix_classCount` — headline certificate: the support digraphs of unreduced
  orthogonal upper Hessenberg matrices are exactly `{ D_n(S) : S }`, counted up
  to isomorphism by the calculator's `countClasses n`. Routes through the entire
  apex — universality (`exists_givensFactorization`), the bridge
  (`digraph_model`), realizability (`completeness`), and rigidity (`rigid`)
  (Paper: Theorem 1 + Theorem 12).

## References

* Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices".
* Li, Severini, "Automation of routine mathematics: a case study".
-/
