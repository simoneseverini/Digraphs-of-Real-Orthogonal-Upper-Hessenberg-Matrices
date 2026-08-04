/-
Copyright (c) 2026 Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Simone Severini
-/
import Util.Linter.MathTag
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Orthogonal matrices

A square real matrix `Q` is *orthogonal* when `Qᵀ · Q = 1`. Mathlib already
provides the orthogonal group `Matrix.orthogonalGroup n ℝ` (a submonoid of the
unitary group), but exposes orthogonality only as a membership condition. For
stating universality-style results — e.g. "every orthogonal upper Hessenberg
matrix is sign-equivalent to a canonical Givens product" — a `Prop`-valued
predicate `Q.IsOrthogonal` reads cleaner than `Q ∈ Matrix.orthogonalGroup n ℝ`.

This file introduces the predicate, the small algebraic API around it, the
bridge to Mathlib's existing `orthogonalGroup`, and the two instances we need
in this project: a Givens rotation is orthogonal, and a finite product of
orthogonal matrices is orthogonal (so any `Matrix.givensProduct θ` is).

## Main definitions

* `Matrix.IsOrthogonal Q` — `Qᵀ · Q = 1`.

## Main results

* `Matrix.IsOrthogonal.mul_self_transpose` — orthogonal matrices also satisfy
  `Q · Qᵀ = 1` (the other-side identity, finite square only).
* `Matrix.IsOrthogonal.transpose`, `.one`, `.mul` — algebraic closure
  properties.
* `Matrix.IsOrthogonal.det_sq` — `(det Q)² = 1`.
* `Matrix.isOrthogonal_iff_mem_orthogonalGroup` — bridge to the existing
  Mathlib API.

The instance lemmas
`Matrix.givensRotation_isOrthogonal`,
`Matrix.givensProduct_isOrthogonal`
are stated where they belong — alongside the rotation and product
definitions in `HessenbergDigraphs.Matrix.Givens.{Basic, Product}` —
which import this file.

## Implementation notes

The predicate is defined in terms of `Qᵀ * Q = 1` rather than
`Q * Qᵀ = 1`; the two are equivalent for finite square matrices via
`Matrix.mul_eq_one_comm` and exchanging via `IsOrthogonal.mul_self_transpose`
is the price of one rewrite. The choice matches the convention in
`Matrix.mem_orthogonalGroup_iff'`.

The file restricts to `ℝ`-coefficients to match the rest of the
formalisation; generalising to a generic `CommRing` with appropriate
`StarRing` is a one-line change in the `def` and follows Mathlib's existing
`unitaryGroup` shape, but is not done here.

## References

Golub & Van Loan, *Matrix Computations* (4th ed.), §1.4 (orthogonal matrices).
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Mathematical layer — paper-side definition of orthogonal matrices
    (Golub & Van Loan §1.4): `Qᵀ · Q = 1`. The choice of "left identity"
    over "right identity" matches Mathlib's `mem_orthogonalGroup_iff'`. -/

/-- **Math.** A square real matrix `Q` is orthogonal if `Qᵀ · Q = 1`. -/
def IsOrthogonal (Q : Matrix n n ℝ) : Prop := Qᵀ * Q = 1

namespace IsOrthogonal

/-! ## Mathematical layer — the other-side identity `Q · Qᵀ = 1` for
    finite square matrices, by `mul_eq_one_comm`. -/

/-- **Math.** Equivalent identity on the other side: `Q · Qᵀ = 1`. -/
theorem mul_self_transpose {Q : Matrix n n ℝ} (h : Q.IsOrthogonal) :
    Q * Qᵀ = 1 :=
  mul_eq_one_comm.mp h

/-! ## Mathematical layer — orthogonality is closed under transposition,
    via the other-side identity `mul_self_transpose`. -/

/-- **Math.** The transpose of an orthogonal matrix is orthogonal. -/
theorem transpose {Q : Matrix n n ℝ} (h : Q.IsOrthogonal) :
    Qᵀ.IsOrthogonal := by
  change Qᵀᵀ * Qᵀ = 1
  rw [Matrix.transpose_transpose]
  exact h.mul_self_transpose

/-! ## Mathematical layer — the identity matrix is orthogonal (base case
    for `IsOrthogonal.list_prod`). -/

/-- **Math.** The identity matrix is orthogonal. -/
theorem one : (1 : Matrix n n ℝ).IsOrthogonal := by
  change (1 : Matrix n n ℝ)ᵀ * 1 = 1
  rw [Matrix.transpose_one, Matrix.one_mul]

/-! ## Mathematical layer — orthogonality is closed under matrix product,
    via `transpose_mul` and middle cancellation `Qᵀ · Q = 1`. -/

/-- **Math.** Product of two orthogonal matrices is orthogonal. -/
theorem mul {Q P : Matrix n n ℝ} (hQ : Q.IsOrthogonal) (hP : P.IsOrthogonal) :
    (Q * P).IsOrthogonal := by
  change (Q * P)ᵀ * (Q * P) = 1
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ Q P, hQ,
    Matrix.one_mul]
  exact hP

/-! ## Mathematical layer — `(det Q)² = 1` for orthogonal `Q`, via
    `det_mul + det_transpose` applied to `Qᵀ · Q = 1`. -/

/-- **Math.** The determinant of an orthogonal matrix squares to one. -/
theorem det_sq {Q : Matrix n n ℝ} (h : Q.IsOrthogonal) :
    Q.det ^ 2 = 1 := by
  have : Qᵀ.det * Q.det = 1 := by
    rw [← Matrix.det_mul, h, Matrix.det_one]
  rw [Matrix.det_transpose] at this
  rw [pow_two]; exact this

/-! ## Mathematical layer — `det Q ∈ {1, -1}` for orthogonal `Q`, by
    factoring `(det Q - 1)(det Q + 1) = 0` from `det_sq`. -/

/-- **Math.** The determinant of an orthogonal matrix is `±1`. -/
theorem det_eq_one_or_neg_one {Q : Matrix n n ℝ} (h : Q.IsOrthogonal) :
    Q.det = 1 ∨ Q.det = -1 := by
  have h2 := h.det_sq
  have : (Q.det - 1) * (Q.det + 1) = 0 := by ring_nf; linarith [h2]
  rcases mul_eq_zero.mp this with h | h
  · left; linarith
  · right; linarith

end IsOrthogonal

/-! ### Bridge to Mathlib's `orthogonalGroup` -/

/-! ## Mathematical layer — bridge to Mathlib's `orthogonalGroup`: the
    project's `IsOrthogonal` predicate is `iff`-equivalent to membership
    in the existing Mathlib subgroup. Lets downstream `IsOrthogonal` API
    interoperate with Mathlib's `orthogonalGroup` machinery when needed. -/

/-- **Math.** `Q` is orthogonal iff it is a member of `Matrix.orthogonalGroup`. -/
theorem isOrthogonal_iff_mem_orthogonalGroup (Q : Matrix n n ℝ) :
    Q.IsOrthogonal ↔ Q ∈ Matrix.orthogonalGroup n ℝ :=
  (Matrix.mem_orthogonalGroup_iff' n ℝ).symm

/-! ### Closure under finite products -/

/-! ## Mathematical layer — orthogonality is closed under finite products,
    by list induction (base: `IsOrthogonal.one`; step: `IsOrthogonal.mul`).
    The result `givensProduct_isOrthogonal` (in `Matrix/Givens/Product.lean`)
    is the principal consumer. -/

/-- **Math.** The product of a finite list of orthogonal matrices is orthogonal. -/
theorem IsOrthogonal.list_prod {n : Type*} [Fintype n] [DecidableEq n]
    (L : List (Matrix n n ℝ)) (hL : ∀ M ∈ L, M.IsOrthogonal) :
    L.prod.IsOrthogonal := by
  induction L with
  | nil => simpa using IsOrthogonal.one
  | cons M tail ih =>
    rw [List.prod_cons]
    exact (hL M (List.mem_cons_self)).mul
      (ih fun M' hM' => hL M' (List.mem_cons_of_mem _ hM'))

end Matrix
