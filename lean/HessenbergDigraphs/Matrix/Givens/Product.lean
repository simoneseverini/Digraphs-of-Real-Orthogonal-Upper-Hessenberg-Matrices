/-
Copyright (c) 2026 Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Matrix.Givens.Rotation
import HessenbergDigraphs.Matrix.Givens.EntryAccess
import HessenbergDigraphs.Matrix.Givens.PartialProduct
import HessenbergDigraphs.Matrix.Hessenberg
import HessenbergDigraphs.Matrix.Orthogonal

/-!
# Ordered Givens product

The canonical ordered Givens product on `Fin n` is

`G_0(θ_0) · G_1(θ_1) · ⋯ · G_{n-2}(θ_{n-2})`

where `G_k(θ_k)` is `Matrix.givensRotation k θ_k`. This product is the model
shape that every orthogonal upper Hessenberg matrix is sign-equivalent to
(see `HessenbergDigraphs.Matrix.Givens.Factorization`).

## Main definitions

* `Matrix.givensProduct θ` — the canonical product as a `Matrix (Fin n) (Fin n) ℝ`.

## Main results

* `Matrix.partialGivensProduct_succ_eq` — peeling off the last factor of a
  prefix product (the recurrence used in every inductive proof below).
* `Matrix.partialGivensProduct_apply_of_row_ge`,
  `Matrix.partialGivensProduct_apply_of_col_ge` — partial products act as the
  identity on rows / columns past their reach.
* `Matrix.givensProduct_isUpperHessenberg` — the canonical product is upper
  Hessenberg.
* `Matrix.givensProduct_apply_subdiag_eq_sin` — closed form for the
  subdiagonal: `(givensProduct θ)[j+1, j] = sin θ_j`.
* `Matrix.givensProduct_apply_subdiag_ne_zero` — under the unreduced
  hypothesis (all `sin θ_k ≠ 0`), every subdiagonal entry is non-zero.

## Implementation notes

The partial product `G_0 · ⋯ · G_{m-1}` is named `Matrix.partialGivensProduct`
and parametrised by the angles as `θ : Fin m → ℝ` (only the actually-used
prefix). The full product `givensProduct θ` is the special case `m = n - 1`.

Several pre-existing lemmas in this file still use the inline form
`(List.ofFn …).prod` in their LHS for historical reasons; migration to
the named form is tracked separately and should not affect the public API
because the two forms are definitionally equal up to `Fin` proof
irrelevance. New lemmas should prefer `partialGivensProduct`.

## References

Golub & Van Loan, *Matrix Computations* (4th ed.), §5.1.
Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" — §2.
-/

namespace Matrix

variable {n : ℕ}

/-! ## Mathematical layer — paper-side definition of the canonical ordered
    Givens product (Golub & Van Loan §5.1; Severini §2). -/

/-- **Math.** The canonical ordered Givens product
`G_0(θ_0) · G_1(θ_1) · ⋯ · G_{n-2}(θ_{n-2})`. -/
noncomputable def givensProduct (θ : Fin (n - 1) → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (List.ofFn fun i : Fin (n - 1) => givensRotation n i (θ i)).prod

section CornerSubmatrix

/-! ## Engineering layer — Type C tool: corner entries of the partial product
    of `m` Givens factors are independent of the ambient dimension `N`
    (any `N ≥ m + 1`). Used by `partialGivensProduct_corner` to identify the
    dim-`(m + 2)` corner submatrix with the canonical dim-`(m + 1)`
    `givensProduct`. -/

/-- **Eng.** The partial product of `m` Givens factors of `θ : Fin m → ℝ` taken in any
ambient dimension `N ≥ m + 1`, evaluated at corner indices `i, j : Fin (m + 1)`,
equals the canonical dim-`(m + 1)` `givensProduct θ`. The proof inducts on `m`,
peeling the last factor and using `partialGivensProduct_apply_of_row_ge` /
`partialGivensProduct_apply_of_col_ge` to discard the high-index slice of the
sum, leaving a bijection between `Fin (m + 1)` (canonical sum) and the filtered
low-index summands of the dim-`N` sum. -/
private lemma partialGivensProduct_apply_corner_eq_givensProduct :
    ∀ (m : ℕ) (θ : Fin m → ℝ) (N : ℕ) (_hN : m + 1 ≤ N) (i j : Fin (m + 1)),
    (List.ofFn fun t : Fin m =>
        givensRotation N ⟨t.val, by have := t.isLt; omega⟩ (θ t)).prod
          ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩
      = givensProduct (n := m + 1) θ i j := by
  intro m
  induction m with
  | zero =>
    intro θ N _ i j
    simp [List.ofFn_zero, List.prod_nil, givensProduct, Matrix.one_apply, Fin.ext_iff]
  | succ p ih =>
    intro θ N hN i j
    have hsplit_LHS : (List.ofFn fun t : Fin (p + 1) =>
            givensRotation N ⟨t.val, by have := t.isLt; omega⟩ (θ t))
        = (List.ofFn fun t : Fin p =>
              givensRotation N ⟨t.val, by have := t.isLt; omega⟩
                (θ ⟨t.val, by have := t.isLt; omega⟩))
          ++ [givensRotation N ⟨p, by omega⟩ (θ ⟨p, by omega⟩)] := by
      rw [List.ofFn_succ_last]; rfl
    rw [hsplit_LHS, List.prod_append, List.prod_singleton, Matrix.mul_apply]
    have hsplit_RHS : givensProduct (n := p + 1 + 1) θ
        = (List.ofFn fun t : Fin p =>
              givensRotation (p + 2) ⟨t.val, by have := t.isLt; omega⟩
                (θ ⟨t.val, by have := t.isLt; omega⟩)).prod *
          givensRotation (p + 2) ⟨p, by omega⟩ (θ ⟨p, by omega⟩) := by
      unfold givensProduct
      change (List.ofFn fun t : Fin (p + 1) =>
          givensRotation (p + 1 + 1) t (θ t)).prod = _
      rw [List.ofFn_succ_last, List.prod_append, List.prod_singleton]
      rfl
    rw [hsplit_RHS, Matrix.mul_apply]
    set Aₙ : Matrix (Fin N) (Fin N) ℝ :=
      (List.ofFn fun t : Fin p =>
        givensRotation N ⟨t.val, by have := t.isLt; omega⟩
          (θ ⟨t.val, by have := t.isLt; omega⟩)).prod with hAₙ
    set Aₘ : Matrix (Fin (p + 2)) (Fin (p + 2)) ℝ :=
      (List.ofFn fun t : Fin p =>
        givensRotation (p + 2) ⟨t.val, by have := t.isLt; omega⟩
          (θ ⟨t.val, by have := t.isLt; omega⟩)).prod with hAₘ
    set Gₙ : Matrix (Fin N) (Fin N) ℝ :=
      givensRotation N ⟨p, by omega⟩ (θ ⟨p, by omega⟩)
    set Gₘ : Matrix (Fin (p + 2)) (Fin (p + 2)) ℝ :=
      givensRotation (p + 2) ⟨p, by omega⟩ (θ ⟨p, by omega⟩)
    have hG_indep : ∀ (a b : ℕ) (ha : a < p + 2) (hb : b < p + 2)
        (haN : a < N) (hbN : b < N),
        Gₙ ⟨a, haN⟩ ⟨b, hbN⟩ = Gₘ ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro a b ha hb haN hbN
      simp only [Gₙ, Gₘ, givensRotation, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply, Fin.ext_iff]
    let θN : Fin (N - 1) → ℝ := fun t =>
      θ ⟨min t.val p, by have := Nat.min_le_right t.val p; omega⟩
    let θM : Fin (p + 2 - 1) → ℝ := fun t =>
      θ ⟨min t.val p, by have := Nat.min_le_right t.val p; omega⟩
    have hθN_eq : ∀ t : Fin p, θN ⟨t.val, by have := t.isLt; omega⟩
        = θ ⟨t.val, by have := t.isLt; omega⟩ := by
      intro t
      simp only [θN]
      congr 1
      have ht : t.val ≤ p := Nat.le_of_lt t.isLt
      ext
      exact Nat.min_eq_left ht
    have hθM_eq : ∀ t : Fin p, θM ⟨t.val, by have := t.isLt; omega⟩
        = θ ⟨t.val, by have := t.isLt; omega⟩ := by
      intro t
      simp only [θM]
      congr 1
      have ht : t.val ≤ p := Nat.le_of_lt t.isLt
      ext
      exact Nat.min_eq_left ht
    have hAₙ_eq : Aₙ = (List.ofFn fun t : Fin p =>
          givensRotation N ⟨t.val, by have := t.isLt; omega⟩
            (θN ⟨t.val, by have := t.isLt; omega⟩)).prod := by
      rw [hAₙ]; simp_rw [← hθN_eq]
    have hAₘ_eq : Aₘ = (List.ofFn fun t : Fin p =>
          givensRotation (p + 2) ⟨t.val, by have := t.isLt; omega⟩
            (θM ⟨t.val, by have := t.isLt; omega⟩)).prod := by
      rw [hAₘ]; simp_rw [← hθM_eq]
    have hA_indep : ∀ (a b : ℕ) (ha : a < p + 2) (hb : b < p + 2)
        (haN : a < N) (hbN : b < N),
        Aₙ ⟨a, haN⟩ ⟨b, hbN⟩ = Aₘ ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro a b ha hb haN hbN
      by_cases hap : a ≥ p + 1
      · rw [hAₙ_eq, hAₘ_eq]
        rw [partialGivensProduct_apply_of_row_ge
            (n := N) θN p (by omega) ⟨a, haN⟩ ⟨b, hbN⟩ hap]
        rw [partialGivensProduct_apply_of_row_ge
            (n := p + 2) θM p (by omega) ⟨a, ha⟩ ⟨b, hb⟩ hap]
        simp [Fin.ext_iff]
      · push_neg at hap
        by_cases hbp : b ≥ p + 1
        · rw [hAₙ_eq, hAₘ_eq]
          rw [partialGivensProduct_apply_of_col_ge
              (n := N) θN p (by omega) ⟨b, hbN⟩ hbp ⟨a, haN⟩]
          rw [partialGivensProduct_apply_of_col_ge
              (n := p + 2) θM p (by omega) ⟨b, hb⟩ hbp ⟨a, ha⟩]
          simp [Fin.ext_iff]
        · push_neg at hbp
          have ihN := ih (fun t : Fin p => θ ⟨t.val, by have := t.isLt; omega⟩) N
            (by omega) ⟨a, by omega⟩ ⟨b, by omega⟩
          have ihM := ih (fun t : Fin p => θ ⟨t.val, by have := t.isLt; omega⟩) (p + 2)
            (by omega) ⟨a, by omega⟩ ⟨b, by omega⟩
          rw [show Aₙ ⟨a, haN⟩ ⟨b, hbN⟩ = _ from ihN]
          rw [show Aₘ ⟨a, ha⟩ ⟨b, hb⟩ = _ from ihM]
    have hi_lt : i.val < p + 2 := i.isLt
    have hj_lt : j.val < p + 2 := j.isLt
    have hi_ltN : i.val < N := by omega
    have hj_ltN : j.val < N := by omega
    have htail : ∀ x : Fin N, x.val ≥ p + 2 →
        Aₙ ⟨i.val, hi_ltN⟩ x * Gₙ x ⟨j.val, hj_ltN⟩ = 0 := by
      intro x hx
      have hxnp : x.val ≠ p := by omega
      have hxnp1 : x.val ≠ p + 1 := by omega
      have : Gₙ x ⟨j.val, hj_ltN⟩ = if x = ⟨j.val, hj_ltN⟩ then 1 else 0 :=
        givensRotation.apply_of_ne_row ⟨p, by omega⟩ _ x ⟨j.val, hj_ltN⟩ hxnp hxnp1
      rw [this]
      have hxne : x ≠ ⟨j.val, hj_ltN⟩ := by
        intro h; rw [h] at hx; simp at hx; omega
      simp [hxne]
    rw [show (Finset.univ : Finset (Fin N)) =
            ((Finset.univ : Finset (Fin N)).filter (fun x => x.val < p + 2))
            ∪ ((Finset.univ : Finset (Fin N)).filter (fun x => ¬ x.val < p + 2)) by
          ext; simp [or_iff_not_imp_left]]
    rw [Finset.sum_union (by
      apply Finset.disjoint_filter.mpr; intros; simp_all)]
    rw [show ((Finset.univ : Finset (Fin N)).filter (fun x => ¬ x.val < p + 2)).sum
            (fun x => Aₙ ⟨i.val, hi_ltN⟩ x * Gₙ x ⟨j.val, hj_ltN⟩) = 0 from by
      apply Finset.sum_eq_zero
      intro x hx
      simp at hx
      exact htail x (by omega)]
    rw [add_zero]
    symm
    refine Finset.sum_nbij'
      (fun (y : Fin (p + 2)) => (⟨y.val, by have := y.isLt; omega⟩ : Fin N))
      (fun (x : Fin N) => (⟨x.val % (p + 2), Nat.mod_lt _ (by omega)⟩ : Fin (p + 2)))
      ?_ ?_ ?_ ?_ ?_
    · intro y _; simp [y.isLt]
    · intro x _; simp
    · intro y _; ext; simp [Nat.mod_eq_of_lt y.isLt]
    · intro x hx; ext
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact Nat.mod_eq_of_lt hx
    · intro y _
      have hy_ltN : y.val < N := by have := y.isLt; omega
      rw [hA_indep i.val y.val hi_lt y.isLt hi_ltN hy_ltN]
      rw [hG_indep y.val j.val y.isLt hj_lt hy_ltN hj_ltN]

/-! ## Mixed — Math: the corner submatrix of the dim-`(m + 2)` partial product
    equals the canonical dim-`(m + 1)` `givensProduct`. | Eng: a 4-line
    specialization of `partialGivensProduct_apply_corner_eq_givensProduct`
    (above) at `N = m + 2`; the heavy dimension-independence machinery lives
    in the helper. -/

/-- **Math.** The partial product of `m` Givens factors of `θ : Fin m → ℝ` taken in
ambient dimension `m + 2`, restricted to the `Fin (m + 1)` corner via the
natural embedding `Fin.castLE`, equals the partial product of the same
factors in the canonical ambient dimension `m + 1` (i.e. `givensProduct θ`).

Each factor's rotation block is contained in `{0, …, m}`, so the last
row/column of the dim-`(m + 2)` partial product is identity; the corner
submatrix is therefore the dim-`(m + 1)` product. -/
theorem partialGivensProduct_corner {m : ℕ} (θ : Fin m → ℝ) :
    (partialGivensProduct (n := m + 2) (by omega : m ≤ m + 2 - 1) θ).submatrix
        (Fin.castLE (Nat.le_succ (m + 1))) (Fin.castLE (Nat.le_succ (m + 1)))
    = givensProduct (n := m + 1) θ := by
  ext i j
  simp only [Matrix.submatrix_apply]
  exact partialGivensProduct_apply_corner_eq_givensProduct m θ (m + 2) (by omega) i j

end CornerSubmatrix

section UpperHessenberg

/-! ## Mixed — Math: right-multiplication by `G_m` extends the upper
    Hessenberg pattern by one column (assuming columns `< m` already
    satisfy Hessenberg and rows `≥ m + 1` are identity). | Eng: case split
    on `j.val ∈ {< m, = m}` and dispatch via `givensRotation.apply_of_ne_col`
    / `apply_of_ne_row`. The IH shape is the loop invariant of the larger
    induction in `givensProduct_isUpperHessenberg`. -/

/-- **Mixed.** Right-multiplying by a Givens matrix extends the Hessenberg property by
one column. If the first `m` columns of `A` satisfy Hessenberg, and rows
`i ≥ m + 1` are identity rows, then the first `m + 1` columns of
`A * G_m` also satisfy Hessenberg. -/
theorem hessenberg_cols_of_mul_givensRotation (θ : Fin (n - 1) → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (hm : m < n - 1)
    (hcols : ∀ i j : Fin n, (j : ℕ) < m → (j : ℕ) + 1 < (i : ℕ) → A i j = 0)
    (hrows : ∀ i j : Fin n, (i : ℕ) ≥ m + 1 → A i j = if i = j then 1 else 0) :
    ∀ i j : Fin n, (j : ℕ) < m + 1 → (j : ℕ) + 1 < (i : ℕ) →
      (A * givensRotation (n := n) ⟨m, by omega⟩ (θ ⟨m, by omega⟩)) i j = 0 := by
  intro i j hjm hij
  simp only [Matrix.mul_apply]
  by_cases hjlt : j.val < m
  · simp_rw [givensRotation.apply_of_ne_col ⟨m, by omega⟩ (θ ⟨m, by omega⟩) _ j
      (by simp; omega) (by simp; omega)]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hcols i j hjlt hij
  · have hjeq : j.val = m := by omega
    simp_rw [hrows i _ (by omega : i.val ≥ m + 1)]
    simp only [boole_mul]
    rw [Fintype.sum_ite_eq]
    have hi1 : i.val ≠ m := by omega
    have hi2 : i.val ≠ m + 1 := by omega
    rw [givensRotation.apply_of_ne_row ⟨m, by omega⟩ (θ ⟨m, by omega⟩) i j hi1 hi2]
    have hij' : i ≠ j := by intro h; simp [Fin.ext_iff] at h; omega
    simp [hij']

/-! ## Mathematical layer — direct application of the column-by-column
    extension to the full canonical product, proved by induction on the
    number of factors via `partialGivensProduct_succ_eq` +
    `hessenberg_cols_of_mul_givensRotation`. -/

/-- **Math.** The canonical Givens product is upper Hessenberg: for `j + 1 < i`,
the `(i, j)` entry vanishes. -/
theorem givensProduct_isUpperHessenberg (θ : Fin (n - 1) → ℝ) :
    IsUpperHessenberg (givensProduct θ) := by
  intro i j hij
  unfold givensProduct
  suffices h : ∀ m (hm : m ≤ n - 1),
      ∀ i j : Fin n, j.val < m → j.val + 1 < i.val →
      (List.ofFn fun t : Fin m =>
          givensRotation n ⟨t.val, by omega⟩ (θ ⟨t.val, by omega⟩)).prod i j = 0 by
    have hjn : j.val < n - 1 := by omega
    exact h (n - 1) le_rfl i j hjn hij
  intro m
  induction m with
  | zero => intro _ i j hjm; omega
  | succ m ih =>
    intro hm i j hjm hij
    have ihm : m ≤ n - 1 := by omega
    have hmlt : m < n - 1 := by omega
    rw [partialGivensProduct_succ_eq θ m hmlt]
    exact hessenberg_cols_of_mul_givensRotation θ _ m hmlt (ih ihm)
      (partialGivensProduct_apply_of_row_ge θ m ihm) i j hjm hij

end UpperHessenberg

section Subdiagonal

/-! ## Mixed — Math: closed form for the subdiagonal entry of the canonical
    product, `(givensProduct θ)[j + 1, j] = sin θ_j` (Golub & Van Loan
    §5.1). | Eng: induction on the number of factors `m` via
    `partialGivensProduct_succ_eq`, dispatching the cases `m = j` (the
    `j`-th rotation contributes the `sin`) and `m ≠ j` (the `j`-th column
    is identity for that factor, so the IH carries through). -/

/-- **Mixed.** Subdiagonal entry of the Givens product equals `sin θ_j`. -/
theorem givensProduct_apply_subdiag_eq_sin (θ : Fin (n - 1) → ℝ)
    (j : Fin n) (hj : (j : ℕ) + 1 < n) :
    givensProduct θ ⟨j + 1, hj⟩ j = Real.sin (θ ⟨↑j, by omega⟩) := by
  unfold givensProduct
  suffices key : ∀ m (hm : m ≤ n - 1), m ≥ j.val + 1 →
      (List.ofFn fun t : Fin m =>
          givensRotation n ⟨t.val, by omega⟩ (θ ⟨t.val, by omega⟩)).prod
        ⟨↑j + 1, hj⟩ j = Real.sin (θ ⟨↑j, by omega⟩) by
    exact key (n - 1) le_rfl (by omega)
  intro m hm hge
  induction m with
  | zero => omega
  | succ m ih =>
    rw [partialGivensProduct_succ_eq θ m hm, Matrix.mul_apply]
    by_cases hmeq : m = j.val
    · have hij1 : (⟨↑j + 1, hj⟩ : Fin n).val ≥ m + 1 := by simp; omega
      simp_rw [partialGivensProduct_apply_of_row_ge θ m (by omega) ⟨↑j + 1, hj⟩ _ hij1]
      simp only [boole_mul]
      rw [Fintype.sum_ite_eq]
      subst hmeq; unfold givensRotation
      simp [Matrix.add_apply, Fin.ext_iff]
    · have hGid : ∀ x, givensRotation (n := n) ⟨m, by omega⟩ (θ ⟨m, by omega⟩) x j =
          if x = j then 1 else 0 := fun x =>
        givensRotation.apply_of_ne_col ⟨m, by omega⟩ _ x j (by simp; omega) (by simp; omega)
      simp_rw [hGid, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      exact ih (by omega) (by omega)

/-! ## Mathematical layer — direct specialization of
    `givensProduct_isUpperHessenberg` to the below-subdiagonal indices
    `j + 1 < i`. -/

/-- **Math.** Below-subdiagonal entries vanish (specialization of
`givensProduct_isUpperHessenberg`). -/
theorem givensProduct_apply_below_subdiag (θ : Fin (n - 1) → ℝ)
    (i j : Fin n) (hij : (j : ℕ) + 1 < (i : ℕ)) :
    givensProduct θ i j = 0 :=
  givensProduct_isUpperHessenberg θ i j hij

/-! ## Mathematical layer — combine `givensProduct_apply_subdiag_eq_sin`
    with the unreduced hypothesis `sin θ_k ≠ 0` to conclude that every
    subdiagonal entry is non-zero. -/

/-- **Math.** Under the unreduced hypothesis `sin θ_k ≠ 0` for all `k`, every
subdiagonal entry of the Givens product is non-zero. -/
private theorem givensProduct_apply_subdiag_ne_zero (θ : Fin (n - 1) → ℝ)
    (hunred : ∀ k : Fin (n - 1), Real.sin (θ k) ≠ 0)
    (j : Fin n) (hj : (j : ℕ) + 1 < n) :
    givensProduct θ ⟨j + 1, hj⟩ j ≠ 0 := by
  rw [givensProduct_apply_subdiag_eq_sin θ j hj]
  exact hunred ⟨↑j, by omega⟩

end Subdiagonal

section Orthogonality

/-! ## Mathematical layer — orthogonality is closed under finite products
    (`IsOrthogonal.list_prod`) and each factor of the canonical product is
    a Givens rotation (`givensRotation_isOrthogonal`). -/

/-- **Math.** The canonical Givens product is orthogonal. Each factor is a Givens
rotation (orthogonal by `givensRotation_isOrthogonal`), and orthogonality is
closed under finite products by `IsOrthogonal.list_prod`. -/
theorem givensProduct_isOrthogonal (θ : Fin (n - 1) → ℝ) :
    (givensProduct θ).IsOrthogonal := by
  unfold givensProduct
  apply IsOrthogonal.list_prod
  intro M hM
  rw [List.mem_ofFn] at hM
  obtain ⟨t, rfl⟩ := hM
  exact givensRotation_isOrthogonal _ _

end Orthogonality

end Matrix
