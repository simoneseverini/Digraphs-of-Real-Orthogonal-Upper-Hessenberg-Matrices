/-
Copyright (c) 2026 Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Matrix.Givens.Rotation
import HessenbergDigraphs.Matrix.Givens.EntryAccess

/-!
# Partial Givens products

The ordered partial product `G_0(θ_0) · G_1(θ_1) · ⋯ · G_{m-1}(θ_{m-1})`
of the first `m` Givens factors in ambient dimension `n`. The bound
`m ≤ n - 1` ensures every rotation index `t : Fin m` lies in the legal
range `Fin (n - 1)` of `givensRotation`'s plane index.

This file develops the row/column identity behaviour of partial products
beyond their reach. The full ordered product `givensProduct θ` (the
`m = n - 1` specialization) and its corner identification with the
canonical product live in the sibling file
`HessenbergDigraphs.Matrix.Givens.Product`.

## Main definitions

* `Matrix.partialGivensProduct hm θ` — the partial Givens product of the
  first `m` factors in ambient dimension `n`.

## Main results

* `Matrix.partialGivensProduct_succ_eq` — peeling off the last factor of
  a prefix product (the recurrence used in every inductive proof
  downstream).
* `Matrix.partialGivensProduct_apply_of_row_ge`,
  `Matrix.partialGivensProduct_apply_of_col_ge` — partial products act
  as the identity on rows / columns past their reach.

## References

Golub & Van Loan, *Matrix Computations* (4th ed.), §5.1.
-/

namespace Matrix

variable {n : ℕ}

/-! ## Engineering layer — Type B index translation: prefix-of-`m`-factors
    product in ambient dimension `n`. The bound `m ≤ n - 1` together with
    the cast `⟨t.val, _⟩ : Fin (n - 1)` for `t : Fin m` packages the
    inclusion `Fin m ⊆ Fin (n - 1)` so the rotation index lies in the
    legal plane range of `givensRotation`. -/

/-- **Eng.** The ordered partial product `G_0(θ_0) · G_1(θ_1) · ⋯ · G_{m-1}(θ_{m-1})`
of the first `m` Givens factors in ambient dimension `n`. The bound
`m ≤ n - 1` ensures every rotation index `t : Fin m` lies in the legal
range `Fin (n - 1)` of `givensRotation`'s plane index.

The full product `givensProduct θ` corresponds to the special case
`m = n - 1`. -/
noncomputable def partialGivensProduct {n m : ℕ} (hm : m ≤ n - 1)
    (θ : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (List.ofFn fun t : Fin m =>
    givensRotation n ⟨t.val, by have := t.isLt; omega⟩ (θ t)).prod

/-! ## Engineering layer — Type C induction tool: peel the last factor off a
    length-`(m + 1)` partial product. The proof is pure list rewriting
    (`List.ofFn_succ_last` + `List.prod_append` + `List.prod_singleton`);
    used by every inductive proof in this file (and by callers in
    `Realization/Propagation.lean` and `Matrix/Givens/Factorization.lean`). -/

/-- **Eng.** The recurrence used by every inductive proof in this file: peeling the
last factor off a length-`m + 1` prefix gives a length-`m` prefix times the
`m`-th Givens factor. -/
theorem partialGivensProduct_succ_eq (θ : Fin (n - 1) → ℝ) (m : ℕ) (hm : m + 1 ≤ n - 1) :
    (List.ofFn fun t : Fin (m + 1) =>
        givensRotation n ⟨t.val, by omega⟩ (θ ⟨t.val, by omega⟩)).prod =
      (List.ofFn fun t : Fin m =>
          givensRotation n ⟨t.val, by omega⟩ (θ ⟨t.val, by omega⟩)).prod *
        givensRotation n ⟨m, by omega⟩ (θ ⟨m, by omega⟩) := by
  rw [List.ofFn_succ_last, List.prod_append, List.prod_singleton]
  congr 1

/-! ### Identity outside the partial-product reach -/

/-! ## Mixed — Math: rows past the partial product's reach are identity rows
    (rotation indices `< m + 1` cannot touch row `i` with `i.val ≥ m + 1`).
    | Eng: induction on `m` + `givensRotation.apply_of_ne_row` to discharge
    each Givens factor's row identity. -/

/-- **Mixed.** The partial Givens product `G_0 · G_1 · ⋯ · G_{m - 1}` acts as the
identity on rows `i` with `i.val ≥ m + 1`. -/
theorem partialGivensProduct_apply_of_row_ge (θ : Fin (n - 1) → ℝ)
    (m : ℕ) (hm : m ≤ n - 1) (i j : Fin n) (hi : i.val ≥ m + 1) :
    (List.ofFn fun t : Fin m =>
        givensRotation n ⟨t.val, by omega⟩ (θ ⟨t.val, by omega⟩)).prod i j =
      if i = j then 1 else 0 := by
  revert j
  induction m with
  | zero => intro j; simp [Matrix.one_apply]
  | succ m ih =>
    intro j
    have ihm : m ≤ n - 1 := by omega
    have him : i.val ≥ m + 1 := by omega
    rw [partialGivensProduct_succ_eq θ m hm, Matrix.mul_apply]
    simp_rw [ih ihm him]
    simp only [boole_mul]
    rw [Fintype.sum_ite_eq]
    rw [givensRotation.apply_of_ne_row ⟨m, by omega⟩ _ i j
      (by simp; omega) (by simp; omega)]

/-! ## Mixed — Math: columns past the partial product's reach are identity
    columns (rotation indices `< m + 1` cannot touch column `j` with
    `j.val ≥ m + 1`). | Eng: induction on `m` + `givensRotation.apply_of_ne_col`. -/

/-- **Mixed.** Columns beyond the first `m` Givens factors are untouched
(identity columns). -/
theorem partialGivensProduct_apply_of_col_ge (θ : Fin (n - 1) → ℝ)
    (m : ℕ) (hm : m ≤ n - 1) (j : Fin n) (hj : j.val ≥ m + 1) (i : Fin n) :
    (List.ofFn fun t : Fin m =>
        givensRotation n ⟨t.val, by omega⟩ (θ ⟨t.val, by omega⟩)).prod i j =
      if i = j then 1 else 0 := by
  induction m with
  | zero => simp [Matrix.one_apply]
  | succ m ih =>
    have ihm : m ≤ n - 1 := by omega
    have hjm : j.val ≥ m + 1 := by omega
    rw [partialGivensProduct_succ_eq θ m hm, Matrix.mul_apply]
    have hne1 : j.val ≠ m := by omega
    have hne2 : j.val ≠ m + 1 := by omega
    simp_rw [givensRotation.apply_of_ne_col ⟨m, by omega⟩ (θ ⟨m, by omega⟩) _ j hne1 hne2]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact ih ihm hjm

end Matrix
