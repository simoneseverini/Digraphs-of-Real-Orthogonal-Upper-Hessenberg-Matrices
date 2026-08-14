/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Real.Basic

/-!
# Support digraph of a square matrix

The *support digraph* of a square matrix records its zero / non-zero pattern:
there is an arc `i → j` exactly when the `(i, j)` entry is non-zero. The notion
is defined for an arbitrary `n × n` real matrix, independent of any
orthogonality or Hessenberg structure; the bundled `OrthogonalHessenberg` view
(`HessenbergDigraphs.Matrix.OrthogonalHessenberg`) re-indexes this to `Vertex n`
for the combinatorial side.

## Main definitions

* `Matrix.supportDigraph M` — the relation `i → j ⟺ M i j ≠ 0` on `Fin n`.

## References

Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" — §3.
-/

namespace Matrix

/-! ## Mathematical layer — the support digraph of a general square matrix:
    arc `i → j` whenever the `(i, j)` entry is non-zero. No orthogonality or
    Hessenberg structure is assumed. -/

/-- **Math.** The support digraph of an `n × n` matrix `M`: the relation
`i → j ⟺ M i j ≠ 0` on `Fin n`. -/
def supportDigraph {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Fin n → Fin n → Prop :=
  fun i j => M i j ≠ 0

end Matrix
