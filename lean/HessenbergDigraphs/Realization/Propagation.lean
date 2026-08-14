/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Vertex
import HessenbergDigraphs.ActiveSet
import HessenbergDigraphs.Realization.ActiveSetOfAngle
import HessenbergDigraphs.Matrix.Givens.Product

/-!
# Propagation of non-zero entries along the Givens product

The "filling" half of the bridge: if `i + 1 ∈ activeRows (activeSet θ)`,
then the partial Givens products `P_{m+1}(i, m+1)` are non-zero for
all `m ≥ i`. The non-vanishing entry propagates one column at a time
because `P_{m+1}(i, m+1)` factors as `P_m(i, m) · (-sin θ_m)` plus
controlled error terms, and `sin θ_m ≠ 0` by the unreduced hypothesis.
The column-freezing lemma makes the propagation translate into the
final upper-triangular non-vanishing claim.

## Main results

* `partialGivensProduct_propagation` — `P_{m+1}(i, m+1) ≠ 0` for
  all `m ≥ i` whenever `i + 1 ∈ activeRows (activeSet θ)`.
* `givensProduct_eq_partial_at_col` — column-freezing: `givensProduct θ`
  agrees with the partial product `P_m` on column `j` once `m ≥ j + 1`.
* `givensProduct_upper_ne_zero_of_arc` — upper-triangular entry is
  non-zero whenever the overlay-arc condition holds.

## References

Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" — §3.
-/

namespace HessenbergDigraphs

open Matrix Finset

variable {n : ℕ} (θ : Fin (n - 1) → ℝ)

/-! ## Mixed — Math: the propagation recurrence
    `P_{m+1}(i, m+1) = -sin(θ_m) · P_m(i, m)` (which is non-zero whenever the
    previous step is non-zero, by the unreduced hypothesis). The base case
    extracts the `(0, 1)`-entry of `G_0(θ_0)` directly; the step folds the
    inductive hypothesis through one Givens layer. | Eng: Type B (Fin↔ℕ
    shifts), `Matrix.mul_apply` + `Finset.sum_eq_single` extraction of the
    pivot column, `givensRotation.apply_of_ne_*` to vanish the off-diagonal
    contributions. List-peel boilerplate absorbed by
    `partialGivensProduct_succ_eq`. -/

/-- **Mixed.** Propagation: under the unreduced hypothesis,
    `P_{m+1}(i, m+1) ≠ 0` for all `m ≥ i` whenever
    `i + 1 ∈ activeRows (activeSet θ)`. The entry propagates via
    `P_{m+1}(i, m+1) = -sin θ_m · P_m(i, m)`. -/
theorem partialGivensProduct_propagation
    (hunred : ∀ k : Fin (n - 1), Real.sin (θ k) ≠ 0)
    (i : Fin n) (hR : Vertex.ofFin i ∈ (activeSet θ).activeRows)
    (m : ℕ) (hm : m < n - 1) (hmi : m ≥ i.val) :
    (List.ofFn (fun t : Fin (m + 1) =>
      givensRotation n ⟨t, by omega⟩ (θ ⟨t, by omega⟩))).prod i ⟨m + 1, by omega⟩ ≠ 0 := by
  induction m with
  | zero =>
    have hieq : i = ⟨0, by omega⟩ := Fin.ext (by simp; omega)
    rw [partialGivensProduct_succ_eq θ 0 hm, Matrix.mul_apply]
    simp only [List.ofFn_zero, List.prod_nil, Matrix.one_apply, boole_mul]
    rw [Fintype.sum_ite_eq]
    unfold givensRotation
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    rw [hieq]
    simp only [zero_add, Fin.mk.injEq, zero_ne_one, ↓reduceIte, and_false, add_zero, and_self,
      one_ne_zero, and_true, ne_eq, neg_eq_zero]
    exact hunred ⟨0, by omega⟩
  | succ m ih =>
    rw [partialGivensProduct_succ_eq θ (m + 1) hm, Matrix.mul_apply]
    set P := (List.ofFn (fun t : Fin (m + 1) =>
        givensRotation n ⟨↑t, by omega⟩ (θ ⟨↑t, by omega⟩))).prod
    suffices hsum : ∑ x : Fin n, P i x *
        givensRotation n ⟨m + 1, by omega⟩ (θ ⟨m + 1, by omega⟩) x ⟨m + 1 + 1, by omega⟩ =
      P i ⟨m + 1, by omega⟩ * (-Real.sin (θ ⟨m + 1, by omega⟩)) by
      rw [hsum]
      apply mul_ne_zero _ (neg_ne_zero.mpr (hunred ⟨m + 1, by omega⟩))
      by_cases hcase : m ≥ i.val
      · exact ih (by omega) hcase
      · have hival : i.val = m + 1 := by omega
        change P i ⟨m + 1, by omega⟩ ≠ 0
        simp only [P]
        rw [partialGivensProduct_succ_eq θ m (by omega), Matrix.mul_apply]
        simp_rw [partialGivensProduct_apply_of_row_ge θ m (by omega) i _ (by simp; omega)]
        simp only [boole_mul]
        rw [Fintype.sum_ite_eq]
        unfold givensRotation
        simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
        have hk1_eq_i : (⟨m + 1, by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
        have hk0_ne_i : (⟨m, by omega⟩ : Fin n) ≠ i := by
          intro h; simp [Fin.ext_iff] at h; omega
        have hk0_ne_m1 : (⟨m, by omega⟩ : Fin n) ≠ ⟨m + 1, by omega⟩ := by
          intro h; simp [Fin.ext_iff] at h
        simp [hk1_eq_i, hk0_ne_i, eq_comm]
        rw [ActiveSet.mem_activeRows_iff] at hR
        unfold activeSet at hR
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hR
        rcases hR with hR1 | ⟨x, ⟨k, hk_cos, hk_eq⟩, ha_eq⟩
        · -- (Vertex.ofFin i).value = 1 forces i.val + 1 = 1, hence i.val = 0,
          -- which contradicts m + 1 = 0 (since m ≥ 0).
          have hofv : (Vertex.ofFin i).value = i.val + 1 := rfl
          have : i.val + 1 = 1 := hofv ▸ hR1
          omega
        · -- hk_eq : ⟨k.val + 1, ...⟩ = x, ha_eq : x.value + 1 = (Vertex.ofFin i).value
          have hxv : x.value = k.val + 1 := by
            have := congrArg Vertex.value hk_eq.symm
            exact this
          have hofv : (Vertex.ofFin i).value = i.val + 1 := rfl
          have : x.value + 1 = i.val + 1 := hofv ▸ ha_eq
          have hkval : (k : ℕ) = m := by omega
          have hkeq2 : (⟨m, by omega⟩ : Fin (n - 1)) = k := Fin.ext (by simp; omega)
          rw [hkeq2]; exact fun h => hk_cos h.symm
    rw [Finset.sum_eq_single ⟨m + 1, by omega⟩]
    · congr 1
      unfold givensRotation
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      simp [Fin.ext_iff]
    · intro x _ hx
      by_cases hx2 : x = ⟨m + 1 + 1, by omega⟩
      · have hPzero : P i x = 0 := by
          simp only [P]
          have hxge : x.val ≥ (m + 1) + 1 := by rw [hx2]
          rw [partialGivensProduct_apply_of_col_ge θ (m + 1) (by omega) x hxge i]
          simp [Fin.ext_iff]; omega
        rw [hPzero, zero_mul]
      · have hGzero : givensRotation n ⟨m + 1, by omega⟩ (θ ⟨m + 1, by omega⟩)
            x ⟨m + 1 + 1, by omega⟩ = 0 := by
          unfold givensRotation
          simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
          have hxm1 : (⟨m + 1, by omega⟩ : Fin n) ≠ x := fun h => hx h.symm
          have hxm2 : (⟨m + 1 + 1, by omega⟩ : Fin n) ≠ x := fun h => hx2 h.symm
          have hx_ne_col : x ≠ ⟨m + 1 + 1, by omega⟩ := hx2
          simp [hxm1, hxm2, hx_ne_col, eq_comm]
        rw [hGzero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

/-! ## Mixed — Math: column freezing — once the partial-product index `m`
    has crossed `j + 1`, every later Givens factor `G_{m'}(θ_{m'})` acts as
    the identity on column `j` (rotation plane is `m' / m' + 1`, both
    indices `≥ j + 1`). | Eng: nested induction on `n` then `m'`,
    `givensRotation.apply_of_ne_col` for the identity action, and
    `Finset.sum_ite_eq'` for the singleton-sum collapse. -/

/-- **Mixed.** Column freezing: the canonical Givens product agrees with the
    partial product `P_m` on column `j` once `m ≥ j + 1`. -/
theorem givensProduct_eq_partial_at_col
    (i j : Fin n) (m : ℕ) (hm : m ≤ n - 1) (hmj : m ≥ j.val + 1) :
    (List.ofFn (fun t : Fin (n - 1) =>
      givensRotation n ⟨t, by omega⟩ (θ ⟨t, by omega⟩))).prod i j =
    (List.ofFn (fun t : Fin m =>
      givensRotation n ⟨t, by omega⟩ (θ ⟨t, by omega⟩))).prod i j := by
  induction n with
  | zero => exact absurd j.isLt (by omega)
  | succ n' =>
    suffices h : ∀ m' : ℕ, (hm' : m' ≤ n') → m' ≥ m →
        (List.ofFn (fun t : Fin m' =>
          givensRotation (n' + 1) ⟨t, Nat.lt_of_lt_of_le t.isLt (by omega)⟩
            (θ ⟨t, Nat.lt_of_lt_of_le t.isLt (by omega)⟩))).prod i j =
        (List.ofFn (fun t : Fin m =>
          givensRotation (n' + 1) ⟨t, by omega⟩ (θ ⟨t, by omega⟩))).prod i j by
      simp only [Nat.succ_sub_one] at hm hmj ⊢
      exact h n' le_rfl (by omega)
    intro m' hm' hm'ge
    induction m' with
    | zero => simp; omega
    | succ m' ih =>
      by_cases hm'eq : m' + 1 = m
      · subst hm'eq; rfl
      · have ihm' : m' ≤ n' := by omega
        have hm'ge' : m' ≥ m := by omega
        rw [partialGivensProduct_succ_eq θ m' hm', Matrix.mul_apply]
        have hne1 : j.val ≠ m' := by omega
        have hne2 : j.val ≠ m' + 1 := by omega
        simp_rw [givensRotation.apply_of_ne_col ⟨m', by omega⟩ (θ ⟨m', by omega⟩) _ j hne1 hne2]
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        exact ih ihm' hm'ge'

/-! ## Mixed — Math: combining propagation + column-freezing yields the
    overlay-arc closed form: every upper-triangular `(i, j)` entry compatible
    with `activeRows × activeCols` is non-zero. The proof splits on whether
    `j + 1` is `n` (boundary case, propagation directly) or strictly less
    (column-freeze first, then propagation/rotation extraction). | Eng: Type B
    (Fin↔ℕ shifts), `Finset.sum_eq_single` to isolate the pivot column,
    `givensRotation.apply_of_ne_*` and explicit ext-bound proofs throughout. -/

/-- **Mixed.** Upper-triangular entry of `givensProduct θ` at `(i, j)` is
    non-zero whenever the overlay arc condition holds:
    `i + 1 ∈ activeRows (activeSet θ)`,
    `j + 1 ∈ activeCols n (activeSet θ)`, and `i ≤ j`. -/
theorem givensProduct_upper_ne_zero_of_arc
    (hunred : ∀ k : Fin (n - 1), Real.sin (θ k) ≠ 0)
    (i j : Fin n) (hij : (i : ℕ) ≤ (j : ℕ))
    (hR : Vertex.ofFin i ∈ (activeSet θ).activeRows)
    (hC : Vertex.ofFin j ∈ (activeSet θ).activeCols) :
    givensProduct θ i j ≠ 0 := by
  unfold Matrix.givensProduct
  rw [ActiveSet.mem_activeCols_iff] at hC
  rcases hC with hC_active | hC_n
  · -- hC_active : ∃ x ∈ (activeSet θ).elements, x.value = (Vertex.ofFin j).value
    unfold activeSet at hC_active
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hC_active
    obtain ⟨x, ⟨k, hk_cos, hk_eq⟩, hxjeq⟩ := hC_active
    have hofjv : (Vertex.ofFin j).value = j.val + 1 := rfl
    have hkjval : k.val = j.val := by
      have h1 : x.value = k.val + 1 := by
        have := congrArg Vertex.value hk_eq.symm
        exact this
      have h2 : x.value = j.val + 1 := by
        have := hxjeq
        rw [hofjv] at this
        exact this
      omega
    have hjlt : j.val < n - 1 := by have := k.isLt; omega
    rw [givensProduct_eq_partial_at_col θ i j (j.val + 1) (by omega) le_rfl]
    have hcos_ne : Real.cos (θ ⟨j.val, hjlt⟩) ≠ 0 := by
      have hkeq : k.val = j.val := by omega
      have : k = ⟨j.val, hjlt⟩ := Fin.ext (by simp; omega)
      rw [← this]; exact hk_cos
    rw [partialGivensProduct_succ_eq θ j.val hjlt, Matrix.mul_apply]
    rw [Finset.sum_eq_single j]
    · apply mul_ne_zero
      · by_cases hij2 : i.val < j.val
        · have := partialGivensProduct_propagation θ hunred i hR (j.val - 1) (by omega) (by omega)
          simp only [Nat.sub_one_add_one_eq_of_pos (by omega : 0 < j.val)] at this
          exact_mod_cast this
        · have hieq : i = j := Fin.ext (by omega)
          rw [hieq]
          by_cases hj0 : j.val = 0
          · simp [hj0, List.ofFn_zero, List.prod_nil]
          · have hsplit2 : (List.ofFn (fun t : Fin j.val =>
                  givensRotation n ⟨↑t, by omega⟩ (θ ⟨↑t, by omega⟩)))
                = (List.ofFn (fun t : Fin (j.val - 1) =>
                    givensRotation n ⟨↑t, by omega⟩ (θ ⟨↑t, by omega⟩)))
                  ++ [givensRotation n ⟨j.val - 1, by omega⟩ (θ ⟨j.val - 1, by omega⟩)] := by
              rw [List.ofFn_congr (show j.val = (j.val - 1) + 1 by omega), List.ofFn_succ_last]
              congr 1
            rw [hsplit2, List.prod_append, List.prod_singleton, Matrix.mul_apply]
            simp_rw [partialGivensProduct_apply_of_row_ge θ (j.val - 1) (by omega) j _ (by omega)]
            simp only [boole_mul]
            rw [Fintype.sum_ite_eq]
            unfold givensRotation
            simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
            have hk1_eq : (⟨j.val - 1 + 1, by omega⟩ : Fin n) = j := by ext; simp; omega
            have hk0_ne : (⟨j.val - 1, by omega⟩ : Fin n) ≠ j := by
              intro h; simp [Fin.ext_iff] at h; omega
            simp [hk1_eq, hk0_ne, eq_comm]
            rw [ActiveSet.mem_activeRows_iff] at hR
            unfold activeSet at hR
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hR
            rcases hR with hR1 | ⟨x, ⟨k', hk'_cos, hk'_eq⟩, ha_eq⟩
            · have hofv : (Vertex.ofFin i).value = i.val + 1 := rfl
              have : i.val + 1 = 1 := hofv ▸ hR1
              omega
            · -- i = j, j ≥ 1; we want k' = ⟨j.val - 1, _⟩
              have hxv : x.value = k'.val + 1 := by
                have := congrArg Vertex.value hk'_eq.symm
                exact this
              have hofv : (Vertex.ofFin i).value = i.val + 1 := rfl
              have : x.value + 1 = i.val + 1 := hofv ▸ ha_eq
              have hkjval : k'.val = i.val - 1 := by omega
              have hieq2 : (⟨j.val - 1, by omega⟩ : Fin (n - 1)) = k' := Fin.ext (by simp; omega)
              rw [hieq2]; exact fun h => hk'_cos h.symm
      · unfold givensRotation
        simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
        have hk1_ne : (⟨j.val + 1, by omega⟩ : Fin n) ≠ j := by
          intro h; simp [Fin.ext_iff] at h
        simp [hk1_ne, eq_comm]
        exact fun h => hcos_ne h.symm
    · intro x _ hxj
      by_cases hx1 : x.val ≥ j.val + 1
      · have : (List.ofFn
            (fun t : Fin j.val => givensRotation n ⟨↑t, by omega⟩ (θ ⟨↑t, by omega⟩))).prod
              i x = 0 := by
          rw [partialGivensProduct_apply_of_col_ge θ j.val (by omega) x (by omega) i]
          simp [Fin.ext_iff]; omega
        rw [this, zero_mul]
      · push_neg at hx1
        have hxlt : x.val < j.val := by omega
        have : givensRotation n ⟨j.val, by omega⟩ (θ ⟨j.val, by omega⟩) x j = 0 := by
          unfold givensRotation
          simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
          have hxk0 : x ≠ (⟨j.val, by omega⟩ : Fin n) := by
            intro h; simp [Fin.ext_iff] at h; omega
          have hxk1 : x ≠ (⟨j.val + 1, by omega⟩ : Fin n) := by
            intro h; simp [Fin.ext_iff] at h; omega
          simp [hxk0, hxk1.symm, Ne.symm hxj]
        rw [this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hjn : j.val + 1 = n := hC_n
    by_cases hn2 : n ≥ 2
    · by_cases hij2 : i.val < j.val
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
        have hjeq : j = ⟨n' + 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [hjeq]
        exact partialGivensProduct_propagation θ hunred i hR n' (by omega) (by simp; omega)
      · have hieqj : i = j := by ext; omega
        subst hieqj
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
        change (List.ofFn fun t : Fin (n' + 1) =>
          givensRotation (n' + 2) ⟨↑t, by omega⟩ (θ ⟨↑t, by omega⟩)).prod i i ≠ 0
        rw [partialGivensProduct_succ_eq θ n' (by omega), Matrix.mul_apply]
        simp_rw [partialGivensProduct_apply_of_row_ge θ n' (by omega) i _ (by omega)]
        simp only [boole_mul]
        rw [Fintype.sum_ite_eq]
        unfold givensRotation
        simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
        have hk0_ne_i : (⟨n', by omega⟩ : Fin (n' + 2)) ≠ i := by
          intro h; simp [Fin.ext_iff] at h; omega
        have hk1_eq_i : (⟨n' + 1, by omega⟩ : Fin (n' + 2)) = i := Fin.ext (by simp; omega)
        simp [hk1_eq_i, hk0_ne_i, eq_comm]
        rw [ActiveSet.mem_activeRows_iff] at hR
        unfold activeSet at hR
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hR
        rcases hR with hR1 | ⟨x, ⟨k, hk_cos, hk_eq⟩, ha_eq⟩
        · have hofv : (Vertex.ofFin i).value = i.val + 1 := rfl
          have : i.val + 1 = 1 := hofv ▸ hR1
          omega
        · have hxv : x.value = k.val + 1 := by
            have := congrArg Vertex.value hk_eq.symm
            exact this
          have hofv : (Vertex.ofFin i).value = i.val + 1 := rfl
          have : x.value + 1 = i.val + 1 := hofv ▸ ha_eq
          have hkval : k.val = n' := by omega
          have heq : (⟨n', by omega⟩ : Fin (n' + 1)) = k := Fin.ext (by simp; omega)
          rw [heq]; exact fun h => hk_cos h.symm
    · have hn1 : n = 1 := by omega
      subst hn1
      have hj0 : j = (0 : Fin 1) := by ext; omega
      have hi0 : i = (0 : Fin 1) := by ext; omega
      subst hj0; subst hi0
      simp [List.ofFn, List.prod_nil]

end HessenbergDigraphs
