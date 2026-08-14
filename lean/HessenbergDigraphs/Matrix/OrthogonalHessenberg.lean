/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Matrix.Orthogonal
import HessenbergDigraphs.Matrix.Hessenberg
import HessenbergDigraphs.Matrix.SignEquivalence
import HessenbergDigraphs.Matrix.SupportDigraph
import HessenbergDigraphs.Vertex
import HessenbergDigraphs.Combinatorial.Digraph

/-!
# OrthogonalHessenberg: bundled real orthogonal upper Hessenberg matrix

`OrthogonalHessenberg n` is the paper-side bundle of an `n × n` real
matrix `Q` together with proofs that `Q` is orthogonal (`Qᵀ · Q = 1`)
and upper Hessenberg (entries strictly below the first subdiagonal
vanish). The legacy interface (`(Q : Matrix (Fin n) (Fin n) ℝ)
(hortho : Q.IsOrthogonal) (hhess : Q.IsUpperHessenberg)`) is preserved
via the structure's three fields.

The underlying matrix is `Matrix (Fin n) (Fin n) ℝ` — Fin-indexed for
compatibility with Mathlib's matrix algebra (`det`, `transpose`, `mul`,
…). Vertex-indexed entry access is provided via the explicit
`Q.apply : Vertex n → Vertex n → ℝ` method (no `CoeFun`, to avoid
`Q i j` ambiguity between the two index conventions).

## Main definitions

* `OrthogonalHessenberg n` — structure with `matrix`, `orthogonal`,
  `hessenberg` fields.
* `OrthogonalHessenberg.apply` — vertex-indexed entry access via
  `Vertex.toFin`.

## Implementation notes

* `matrix : Matrix (Fin n) (Fin n) ℝ` — Fin-indexed for Mathlib
  compatibility. Replacing this with `Matrix (Vertex n) (Vertex n) ℝ`
  would lose access to `Matrix.det`, `Matrix.transpose_*`, etc.
* `apply` is a one-line `def` rather than a `CoeFun` instance: a
  `CoeFun` would let `Q i j` work for `i j : Vertex n` but also for
  `i j : Fin n` (via `.matrix`), creating two distinct entry-access
  paths. The explicit `Q.apply v w` keeps the two conventions
  syntactically distinguishable.

## References

Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" — §1
(unreduced orthogonal upper Hessenberg matrices).
-/

namespace HessenbergDigraphs

/-! ## Mathematical layer — paper-side bundle: an orthogonal upper
    Hessenberg matrix `Q` is a `Matrix (Fin n) (Fin n) ℝ` together with
    proofs of `Qᵀ · Q = 1` and the Hessenberg property `M[i, j] = 0`
    when `j + 1 < i`. Combines what the legacy interface threaded as
    three separate parameters (matrix + `IsOrthogonal` + `IsUpperHessenberg`). -/

/-- **Math.** A real `n × n` orthogonal upper Hessenberg matrix: bundles the
underlying matrix together with the orthogonality and Hessenberg
proofs. Index type is `Fin n` (for Mathlib matrix-algebra
compatibility); use `Q.apply` for vertex-indexed entry access. -/
@[ext]
structure OrthogonalHessenberg (n : ℕ) where
  matrix : Matrix (Fin n) (Fin n) ℝ
  orthogonal : matrix.IsOrthogonal
  hessenberg : matrix.IsUpperHessenberg

namespace OrthogonalHessenberg

variable {n : ℕ}

/-! ## Engineering layer — Type B vertex-indexed entry access. The legacy
    `Q.matrix i j` (with `i j : Fin n`) stays available; `Q.apply v w`
    (with `v w : Vertex n`) provides the paper-aligned form via
    `Vertex.toFin`. -/

/-- **Eng.** Vertex-indexed matrix entry access:
`Q.apply i j = Q.matrix i.toFin j.toFin`. -/
def apply (Q : OrthogonalHessenberg n) (i j : Vertex n) : ℝ :=
  Q.matrix i.toFin j.toFin

/-! ## Mathematical layer — demonstration: vertex-indexed below-subdiagonal
    entries vanish. The legacy `Q.IsUpperHessenberg` predicate is stated
    in `Fin n` indices; this restates it for `Vertex n`. -/

/-- **Math.** For an orthogonal upper Hessenberg `Q`, vertex-indexed entries below
the subdiagonal vanish: when `j.value + 1 < i.value`, `Q.apply i j = 0`. -/
theorem apply_of_below_subdiag (Q : OrthogonalHessenberg n) (i j : Vertex n)
    (h : j.value + 1 < i.value) : Q.apply i j = 0 := by
  unfold apply
  apply Q.hessenberg
  show j.toFin.val + 1 < i.toFin.val
  change (j.value - 1) + 1 < (i.value - 1)
  have := i.one_le_value
  have := j.one_le_value
  omega

/-! ## Engineering layer — `CoeFun` instance: write `Q i j` for
    `OrthogonalHessenberg.apply Q i j` (Vertex-indexed entry access).
    Does not collide with `Matrix _ _ _` indexing because the carriers
    are different types. -/

/-- **Eng.** Vertex-indexed function-application sugar: `Q i j` desugars to
`Q.apply i j`. Lets paper-side proofs read like the paper sentences,
without explicit `.apply` plumbing. -/
instance : CoeFun (OrthogonalHessenberg n) (fun _ => Vertex n → Vertex n → ℝ) :=
  ⟨OrthogonalHessenberg.apply⟩

end OrthogonalHessenberg

/-! ## Mathematical layer — paper-side support digraph view: a vertex pair
    `(i, j)` is in `supportDigraph Q` iff the corresponding entry `Q i j` is
    non-zero. Specialises `Matrix.supportDigraph` to the bundled
    `OrthogonalHessenberg`, re-indexed to `Vertex n` (Severini §3). -/

/-- **Math.** The support digraph of `Q : OrthogonalHessenberg n`, the
specialisation of `Matrix.supportDigraph Q.matrix` re-indexed to `Vertex n`. -/
def OrthogonalHessenberg.supportDigraph (Q : OrthogonalHessenberg n) : Digraph n :=
  fun i j => Q.matrix.supportDigraph i.toFin j.toFin

/-- **Math.** Pointwise unfolding of `supportDigraph`: `(i, j) ∈ supportDigraph Q`
iff `Q.apply i j ≠ 0`, by definition. -/
@[simp] theorem OrthogonalHessenberg.supportDigraph_iff_apply_ne_zero
    (Q : OrthogonalHessenberg n) (i j : Vertex n) :
    Q.supportDigraph i j ↔ Q.apply i j ≠ 0 := Iff.rfl

/-! ## Mathematical layer — bundled-structure sign equivalence between
    bundled `OrthogonalHessenberg` matrices, lifted from the Mathlib-side
    `Matrix.SignEquiv` (Severini Lemma 1). -/

/-- **Math.** Two `OrthogonalHessenberg n` matrices are sign-equivalent if their
underlying `Matrix` representations are sign-equivalent. -/
def OrthogonalHessenberg.signEquivTo (Q Q' : OrthogonalHessenberg n) : Prop :=
  Matrix.SignEquiv Q.matrix Q'.matrix

/-- **Math.** Sign-equivalent bundled matrices have the same support digraph,
the `Vertex`-indexed specialisation of `Matrix.supportDigraph_eq_of_signEquiv`. -/
theorem OrthogonalHessenberg.supportDigraph_eq_of_signEquivTo
    {Q Q' : OrthogonalHessenberg n} (h : Q.signEquivTo Q') :
    Q.supportDigraph = Q'.supportDigraph := by
  funext i j
  have hm : Q.matrix.supportDigraph = Q'.matrix.supportDigraph :=
    Matrix.supportDigraph_eq_of_signEquiv h
  exact congrFun (congrFun hm i.toFin) j.toFin

/-! ## Mathematical layer — paper-side `Q` is *unreduced* iff every
    spine entry `(j+1, j)` is non-zero (Severini §1; Golub & Van Loan §7.4).
    Vertex-indexed predicate on bundled `OrthogonalHessenberg`. -/

/-- **Math.** A bundled `OrthogonalHessenberg n` is unreduced iff every spine entry
`Q.apply (j.next h) j` is non-zero. -/
def OrthogonalHessenberg.IsUnreduced (Q : OrthogonalHessenberg n) : Prop :=
  ∀ j : Vertex n, (h : j.value < n) → Q.apply (j.next h) j ≠ 0

/-- **Eng.** Paper-side notation for bundled-structure sign equivalence between
bundled orthogonal Hessenberg matrices. Scoped to `HessenbergDigraphs`
to avoid colliding with the matrix-side `Matrix.≃sign`. -/
scoped infix:50 " ≃sign " => OrthogonalHessenberg.signEquivTo

end HessenbergDigraphs
