/-
Copyright (c) 2026 Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Matrix.Givens.Rotation

/-!
# Entry-level access for Givens rotations

Entry-by-entry API for `Matrix.givensRotation k θ`: the four entries of
the `2 × 2` rotation block, the identity behaviour off the block (by
row or by column), and the commutation with `Matrix.diagonal d` when
`d` agrees on the rotation pair.

Each entry-level lemma is proved by `simp only` on a small explicit
list of `Matrix.single`/`Matrix.one`/`Matrix.add` apply rules, never
by `simp_all` or `decide`, so the API can be invoked from `simp only`
calls upstream without triggering heavy elaboration.

The `givensRotation` definition itself and the orthogonality result
(`givensRotation_orthogonal`, `givensRotation_isOrthogonal`) live in
the sibling file `HessenbergDigraphs.Matrix.Givens.Rotation`.

## Main results

* `Matrix.givensRotation.apply_self_self`,
  `Matrix.givensRotation.apply_succ_self`,
  `Matrix.givensRotation.apply_self_succ`,
  `Matrix.givensRotation.apply_succ_succ` — the four entries of the
  `2 × 2` rotation block.
* `Matrix.givensRotation.apply_of_ne_row`,
  `Matrix.givensRotation.apply_of_ne_col` — the rotation acts as
  identity off the block.
* `Matrix.givensRotation_commute_diagonal_of_eq_on_rotation_pair` —
  commutation with a diagonal matrix that agrees on the rotation pair.

## References

Golub & Van Loan, *Matrix Computations* (4th ed.), §5.1.
-/

namespace Matrix

namespace givensRotation

/-! ### Entry-level API

Each lemma below pins down a single entry of `givensRotation k θ` by explicit
case analysis on the indices. The proofs use only `simp only` with the named
`Matrix.{add,one,single}_apply` rules — no `simp_all`, no `decide`.
-/

/-! ## Mixed — Math: top-left entry of the rotation block is `cos θ`.
    | Eng: explicit `unfold + simp only [Matrix.{add, one, single}_apply]`
    (avoiding `simp_all` per the file's discipline that this entry-level
    API stays cheap to invoke from upstream `simp only` calls). -/

/-- **Mixed.** Top-left of the `2 × 2` block: `G k k = cos θ`. -/
theorem apply_self_self {n : ℕ} (k : Fin (n - 1)) (θ : ℝ) :
    givensRotation n k θ ⟨k.val, by omega⟩ ⟨k.val, by omega⟩ = Real.cos θ := by
  unfold givensRotation
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  simp [eq_comm]

/-! ## Mixed — Math: bottom-left entry of the rotation block is `sin θ`.
    | Eng: same shape as `apply_self_self`. -/

/-- **Mixed.** Bottom-left of the `2 × 2` block: `G (k + 1) k = sin θ`. -/
theorem apply_succ_self {n : ℕ} (k : Fin (n - 1)) (θ : ℝ) :
    givensRotation n k θ ⟨k.val + 1, by omega⟩ ⟨k.val, by omega⟩ = Real.sin θ := by
  unfold givensRotation
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  simp [eq_comm]

/-! ## Mixed — Math: top-right entry of the rotation block is `-sin θ`.
    | Eng: same shape as `apply_self_self`. -/

/-- **Mixed.** Top-right of the `2 × 2` block: `G k (k + 1) = -sin θ`. -/
theorem apply_self_succ {n : ℕ} (k : Fin (n - 1)) (θ : ℝ) :
    givensRotation n k θ ⟨k.val, by omega⟩ ⟨k.val + 1, by omega⟩ = -Real.sin θ := by
  unfold givensRotation
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  simp [eq_comm]

/-! ## Mixed — Math: bottom-right entry of the rotation block is `cos θ`.
    | Eng: same shape as `apply_self_self`. -/

/-- **Mixed.** Bottom-right of the `2 × 2` block: `G (k + 1) (k + 1) = cos θ`. -/
theorem apply_succ_succ {n : ℕ} (k : Fin (n - 1)) (θ : ℝ) :
    givensRotation n k θ ⟨k.val + 1, by omega⟩ ⟨k.val + 1, by omega⟩ = Real.cos θ := by
  unfold givensRotation
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  simp [eq_comm]

/-! ## Mixed — Math: the rotation acts as identity on columns away from
    `{k, k + 1}` (the column index lies outside the rotation block).
    | Eng: dispatch the four `Matrix.single` summands by `Fin.ext_iff` on
    the index inequalities, leaving only the identity contribution. -/

/-- **Mixed.** The Givens rotation is the identity outside its `2 × 2` block when restricted
to a column away from `{k, k + 1}`. -/
theorem apply_of_ne_col {n : ℕ} (k : Fin (n - 1)) (θ : ℝ)
    (i j : Fin n) (hj1 : j.val ≠ k.val) (hj2 : j.val ≠ k.val + 1) :
    givensRotation n k θ i j = if i = j then 1 else 0 := by
  unfold givensRotation
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have h1 : (⟨k.val, by omega⟩ : Fin n) ≠ j := fun h => by
    simp only [Fin.ext_iff] at h; exact hj1 h.symm
  have h2 : (⟨k.val + 1, by omega⟩ : Fin n) ≠ j := fun h => by
    simp only [Fin.ext_iff] at h; exact hj2 h.symm
  simp [Ne.symm h1, Ne.symm h2, eq_comm]

/-! ## Mixed — Math: the rotation acts as identity on rows away from
    `{k, k + 1}` (the row index lies outside the rotation block).
    | Eng: same shape as `apply_of_ne_col`. -/

/-- **Mixed.** The Givens rotation is the identity outside its `2 × 2` block when restricted
to a row away from `{k, k + 1}`. -/
theorem apply_of_ne_row {n : ℕ} (k : Fin (n - 1)) (θ : ℝ)
    (i j : Fin n) (hi1 : i.val ≠ k.val) (hi2 : i.val ≠ k.val + 1) :
    givensRotation n k θ i j = if i = j then 1 else 0 := by
  unfold givensRotation
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have h1 : i ≠ (⟨k.val, by omega⟩ : Fin n) := fun h => by
    simp only [Fin.ext_iff] at h; exact hi1 h
  have h2 : i ≠ (⟨k.val + 1, by omega⟩ : Fin n) := fun h => by
    simp only [Fin.ext_iff] at h; exact hi2 h
  simp [h1, h2, eq_comm]

end givensRotation

/-! ### Commutation with diagonal matrices -/

/-! ## Engineering layer — Type B index translation: under the hypothesis
    `d k.castSucc = d k.succ`, the diagonal `d` takes the value
    `d k.castSucc` on any index `i : Fin (m + 1)` with
    `i.val ∈ {k.val, k.val + 1}`. Bridges the `i.val = ...` form (which
    arises naturally from `by_cases` on `i.val = k.val ∨ i.val = k.val + 1`)
    to the `i = k.castSucc / k.succ` form (needed to invoke `hd`). -/

/-- **Eng.** If `i : Fin (m + 1)` is one of the two rotation-block indices of
`k : Fin m` (i.e. `i.val = k.val` or `i.val = k.val + 1`), and `d` agrees
on the rotation pair `(k.castSucc, k.succ)`, then `d i = d k.castSucc`. -/
private lemma diagonal_const_on_rotation_block {m : ℕ} (k : Fin m)
    (d : Fin (m + 1) → ℝ) (hd : d k.castSucc = d k.succ)
    (i : Fin (m + 1)) (hi : i.val = k.val ∨ i.val = k.val + 1) :
    d i = d k.castSucc := by
  rcases hi with h | h
  · have : i = k.castSucc := Fin.ext h
    rw [this]
  · have : i = k.succ := Fin.ext h
    rw [this, hd]

/-! ## Mixed — Math: a Givens rotation in plane `(k.castSucc, k.succ)`
    commutes with `Matrix.diagonal d` when `d` agrees on the rotation
    pair. Entry-wise reasoning: off the rotation block the rotation is
    identity (commutes with anything); on the block the diagonal is
    constant (so the commutator vanishes). | Eng: `ext i j` +
    `Finset.sum_eq_single` to collapse the diagonal sums to
    `G i j * d j = d i * G i j`; then a 2×2 `by_cases` on `(i, j) ∈ block`
    dispatches via `diagonal_const_on_rotation_block` (in-block case) or
    `givensRotation.apply_of_ne_{row, col}` (out-of-block case). -/

/-- **Mixed.** A Givens rotation `givensRotation (m + 1) k θ` commutes with `diagonal d`
when `d` agrees on the rotation pair `(k.castSucc, k.succ)`. The rotation's
non-trivial off-diagonal entries lie at `(k.castSucc, k.succ)` and
`(k.succ, k.castSucc)`, so the commutation identity reduces to
`d k.castSucc = d k.succ` after entry-wise expansion. -/
theorem givensRotation_commute_diagonal_of_eq_on_rotation_pair {m : ℕ}
    (k : Fin m) (θ : ℝ) (d : Fin (m + 1) → ℝ)
    (hd : d k.castSucc = d k.succ) :
    givensRotation (m + 1) k θ * Matrix.diagonal d
      = Matrix.diagonal d * givensRotation (m + 1) k θ := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.diagonal_apply]
  rw [Finset.sum_eq_single j
    (fun b _ hb => by rw [if_neg hb, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [Finset.sum_eq_single i
    (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [if_pos rfl, if_pos rfl]
  -- Goal: G i j * d j = d i * G i j
  by_cases hi_block : i.val = k.val ∨ i.val = k.val + 1
  · by_cases hj_block : j.val = k.val ∨ j.val = k.val + 1
    · -- Both in block: d takes the same value at i, j (both = d k.castSucc).
      rw [diagonal_const_on_rotation_block k d hd i hi_block,
          diagonal_const_on_rotation_block k d hd j hj_block]
      ring
    · -- j outside block: G i j = if i = j then 1 else 0
      push Not at hj_block
      rw [givensRotation.apply_of_ne_col (n := m + 1) k θ i j hj_block.1 hj_block.2]
      by_cases hij : i = j
      · subst hij; ring
      · simp [hij]
  · -- i outside block: G i j = if i = j then 1 else 0
    push Not at hi_block
    rw [givensRotation.apply_of_ne_row (n := m + 1) k θ i j hi_block.1 hi_block.2]
    by_cases hij : i = j
    · subst hij; ring
    · simp [hij]

end Matrix
