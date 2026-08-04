/-
Copyright (c) 2026 Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Simone Severini
-/
import Util.Linter.MathTag
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Linarith
import HessenbergDigraphs.Matrix.Orthogonal

/-!
# Givens rotations

A Givens rotation in the `(k, k + 1)` plane on `Fin n` is the identity matrix with
its `2 × 2` principal submatrix at rows/columns `k, k + 1` replaced by the planar
rotation `[[cos θ, -sin θ], [sin θ, cos θ]]`. It is the basic building block of
Hessenberg reductions and the QR algorithm.

This file defines a single Givens rotation and proves it orthogonal. The
entry-level access lemmas (the `2 × 2` block entries and off-block vanishing)
live in the sibling file `HessenbergDigraphs.Matrix.Givens.EntryAccess`; the
ordered product `G_0 · G_1 · ⋯ · G_{n-2}` lives in
`HessenbergDigraphs.Matrix.Givens.Product`.

## Main definitions

* `Matrix.givensRotation k θ` — the `(k, k + 1)`-plane Givens rotation as an
  `n × n` matrix over `ℝ`.

## Main results

* `Matrix.givensRotation_orthogonal` — `Gᵀ · G = 1`.
* `Matrix.givensRotation_isOrthogonal` — the same fact repackaged into the
  project's `IsOrthogonal` predicate.

## Implementation notes

The matrix is built as a sum of `Matrix.single` perturbations on top of the
identity. Each entry-level lemma is proved by `simp only` on a small explicit
list of `Matrix.single`/`Matrix.one`/`Matrix.add` apply rules, never by
`simp_all` or `decide`, so the API can be used from `simp only` calls upstream
without triggering heavy elaboration.

## References

Golub & Van Loan, *Matrix Computations* (4th ed.), §5.1.
-/

namespace Matrix

/-! ## Mathematical layer — paper-side definition of the Givens rotation in
    the `(k, k + 1)` plane (Golub & Van Loan §5.1; the basic building block
    of QR / Hessenberg reduction). Built as `1 + 4 × Matrix.single`
    perturbations on the rotation block. -/

/-- **Math.** The Givens rotation in the `(k, k + 1)` plane with angle `θ`: the identity
matrix with the `2 × 2` block at rows/columns `k, k + 1` replaced by the planar
rotation `[[cos θ, -sin θ], [sin θ, cos θ]]`.

The dimension `n` is taken explicitly because the relevant `n` is rarely
inferable from the type of `k` alone in downstream uses (the `θ` argument may
be defined via a `Fin (n-1) → ℝ` whose `n` ambiguity already triggered
elaboration failures in earlier drafts of this API). -/
noncomputable def givensRotation (n : ℕ) (k : Fin (n - 1)) (θ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  let k0 : Fin n := ⟨k, by omega⟩
  let k1 : Fin n := ⟨k + 1, by omega⟩
  (1 : Matrix (Fin n) (Fin n) ℝ)
    + Matrix.single k0 k0 (Real.cos θ - 1)
    + Matrix.single k0 k1 (-Real.sin θ)
    + Matrix.single k1 k0 (Real.sin θ)
    + Matrix.single k1 k1 (Real.cos θ - 1)

/-! ### Orthogonality -/

/-! ## Mixed — Math: `Gᵀ · G = 1`, the Givens rotation is orthogonal
    (Golub & Van Loan §5.1). | Eng: `transpose_add` /
    `single_mul_single_{same, of_ne}` rewrites collapse the product to a
    sparse 2×2 contribution; then a 4-way `by_cases` on
    `(i, j) ∈ {k0, k1} × {k0, k1}` is closed by
    `nlinarith [Real.sin_sq_add_cos_sq θ]`. -/

/-- **Mixed.** Givens rotations are orthogonal: `Gᵀ · G = 1`. -/
theorem givensRotation_orthogonal {n : ℕ} (k : Fin (n - 1)) (θ : ℝ) :
    (givensRotation n k θ)ᵀ * givensRotation n k θ = 1 := by
  unfold givensRotation
  set k0 : Fin n := ⟨↑k, by omega⟩
  set k1 : Fin n := ⟨↑k + 1, by omega⟩
  have hne : k0 ≠ k1 := fun h => by simp [k0, k1, Fin.ext_iff] at h
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul]
  simp only [Matrix.single_mul_single_same]
  simp only [Matrix.single_mul_single_of_ne _ _ _ _ hne,
    Matrix.single_mul_single_of_ne _ _ _ _ hne.symm]
  ext i j
  simp only [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, zero_apply]
  by_cases hi0 : k0 = i <;> by_cases hi1 : k1 = i <;>
    by_cases hj0 : k0 = j <;> by_cases hj1 : k1 = j <;>
    simp_all <;> nlinarith [Real.sin_sq_add_cos_sq θ]

/-! ## Mathematical layer — repackage `givensRotation_orthogonal` into the
    `IsOrthogonal` predicate (one-line wrapper for downstream API). -/

/-- **Math.** Givens rotations satisfy the `IsOrthogonal` predicate. -/
theorem givensRotation_isOrthogonal {n : ℕ} (k : Fin (n - 1)) (θ : ℝ) :
    (givensRotation n k θ).IsOrthogonal :=
  givensRotation_orthogonal k θ

end Matrix
