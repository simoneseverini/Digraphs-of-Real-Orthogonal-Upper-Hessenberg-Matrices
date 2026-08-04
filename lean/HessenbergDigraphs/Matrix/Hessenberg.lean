/-
Copyright (c) 2026 Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Simone Severini
-/
import Util.Linter.MathTag
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Real.Basic

/-!
# Upper Hessenberg matrices

A square matrix is *upper Hessenberg* if every entry strictly below the first
subdiagonal is zero. It is *unreduced* if additionally every subdiagonal entry
is non-zero.

The two predicates underlie the QR algorithm and the classification of support
digraphs of orthogonal Hessenberg matrices.

## Main definitions

* `Matrix.IsUpperHessenberg M` — `M i j = 0` whenever `j + 1 < i`.
* `Matrix.IsUnreduced M` — upper Hessenberg with non-vanishing subdiagonal.

## References

Golub & Van Loan, *Matrix Computations* (4th ed.), §7.4.
Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" — §1.
-/

namespace Matrix

/-! ## Mathematical layer — paper-side definition: upper Hessenberg means
    every entry strictly below the first subdiagonal vanishes
    (Golub & Van Loan §7.4; Severini §1). -/

/-- **Math.** A matrix is upper Hessenberg if all entries below the first subdiagonal
are zero, i.e. `M i j = 0` whenever `j + 1 < i`. -/
def IsUpperHessenberg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, (j : ℕ) + 1 < (i : ℕ) → M i j = 0

/-! ## Mathematical layer — paper-side definition: an upper Hessenberg
    matrix is *unreduced* if every subdiagonal entry is non-zero
    (Golub & Van Loan §7.4; Severini §1). The unreduced hypothesis is
    what underlies the QR algorithm's irreducibility / shift-step
    behaviour. -/

/-- **Math.** An upper Hessenberg matrix is unreduced if all subdiagonal entries are
non-zero, i.e. `M (i + 1) i ≠ 0` for all valid `i`. -/
def IsUnreduced {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsUpperHessenberg M ∧
  ∀ i : Fin n, (h : (i : ℕ) + 1 < n) → M ⟨i + 1, h⟩ i ≠ 0

end Matrix
