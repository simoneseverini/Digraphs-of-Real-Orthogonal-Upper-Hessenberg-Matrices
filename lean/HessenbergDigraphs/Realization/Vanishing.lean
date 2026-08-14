/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import Mathlib.Analysis.RCLike.Basic
import HessenbergDigraphs.Vertex
import HessenbergDigraphs.ActiveSet
import HessenbergDigraphs.Realization.ActiveSetOfAngle
import HessenbergDigraphs.Matrix.Givens.Product

/-!
# Row and column vanishing for the Givens product (bundled-structure form)

If `Vertex.ofFin i ∉ (activeSet θ).activeRows` (resp. column not in
`(activeSet θ).activeCols`), every upper-triangular entry in that row
(resp. column) of the Givens product is zero.

## References

Severini — §3.
-/

namespace HessenbergDigraphs

open Matrix Finset

variable {n : ℕ} (θ : Fin (n - 1) → ℝ)

/-- **Mixed.** Row vanishing: if the paper-side row label `i + 1` is not in
`(activeSet θ).activeRows`, the upper-triangular part of row `i` is
identically zero. -/
theorem givensProduct_row_vanishing
    (_hunred : ∀ k : Fin (n - 1), Real.sin (θ k) ≠ 0)
    (i j : Fin n) (hij : (i : ℕ) ≤ (j : ℕ))
    (hR : Vertex.ofFin i ∉ (activeSet θ).activeRows) :
    givensProduct θ i j = 0 := by
  rw [ActiveSet.mem_activeRows_iff] at hR
  push Not at hR
  obtain ⟨hine1, hnotactive⟩ := hR
  have hofv : (Vertex.ofFin i).value = i.val + 1 := rfl
  have hpos : 0 < i.val := by
    have : i.val + 1 ≠ 1 := hofv ▸ hine1
    omega
  have hibound : i.val - 1 < n - 1 := by omega
  have hcos0 : Real.cos (θ ⟨i.val - 1, hibound⟩) = 0 := by
    by_contra hne
    -- Build the element of activeSet's elements with value i.val
    let k : Vertex (n - 1) :=
      ⟨i.val, by omega, by omega⟩
    have hk_in_elements : k ∈ (activeSet θ).elements := by
      unfold activeSet
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨i.val - 1, hibound⟩, hne, ?_⟩
      ext
      change i.val - 1 + 1 = i.val
      omega
    exact hnotactive k hk_in_elements rfl
  unfold Matrix.givensProduct
  suffices key : ∀ m (hm : m ≤ n - 1), m ≥ i.val → ∀ col : Fin n, col.val ≥ i.val →
      (List.ofFn (fun t : Fin m => givensRotation n ⟨t, by omega⟩ (θ ⟨t, by omega⟩))).prod
        i col = 0 by
    exact key (n - 1) le_rfl (by omega) j hij
  intro m
  induction m with
  | zero => intro _ hge; omega
  | succ m ih =>
    intro hm hge col hcol
    rw [partialGivensProduct_succ_eq θ m hm, Matrix.mul_apply]
    by_cases hmeq : m + 1 = i.val
    · have hid : ∀ x : Fin n,
          (List.ofFn (fun t : Fin m => givensRotation n ⟨t, by omega⟩ (θ ⟨t, by omega⟩))).prod i x =
            if i = x then 1 else 0 :=
        fun x => partialGivensProduct_apply_of_row_ge θ m (by omega) i x (by omega)
      simp_rw [hid, boole_mul]
      rw [Fintype.sum_ite_eq]
      unfold givensRotation
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      have hk0_ne_col : (⟨m, by omega⟩ : Fin n) ≠ col := by
        intro h; simp [Fin.ext_iff] at h; omega
      have hk1_eq_i : (⟨m + 1, by omega⟩ : Fin n) = i := by
        ext; simp; omega
      have hk0_ne_i : (⟨m, by omega⟩ : Fin n) ≠ i := by
        intro h; simp [Fin.ext_iff] at h; omega
      by_cases hicol : i = col
      · subst hicol
        simp [hk0_ne_i, hk1_eq_i, eq_comm]
        have : (⟨m, by omega⟩ : Fin (n - 1)) = ⟨i.val - 1, hibound⟩ := by
          ext; simp; omega
        rw [this]; linarith
      · simp [hk0_ne_col.symm, hk0_ne_i, hk1_eq_i, hicol, eq_comm]
    · apply Finset.sum_eq_zero
      intro x _
      by_cases hxi : x.val ≥ i.val
      · have := ih (by omega) (by omega) x hxi
        rw [this, zero_mul]
      · push Not at hxi
        have hGid : givensRotation n ⟨m, by omega⟩ (θ ⟨m, by omega⟩) x col = 0 := by
          rw [givensRotation.apply_of_ne_row ⟨m, by omega⟩ _ x col
                (by simp; omega) (by simp; omega),
              if_neg (show x ≠ col by intro h; subst h; omega)]
        rw [hGid, mul_zero]

/-- **Mixed.** Column vanishing: if `Vertex.ofFin j ∉ (activeSet θ).activeCols`, the
upper-triangular part of column `j` is identically zero. -/
theorem givensProduct_col_vanishing
    (_hunred : ∀ k : Fin (n - 1), Real.sin (θ k) ≠ 0)
    (i j : Fin n) (hij : (i : ℕ) ≤ (j : ℕ))
    (hC : Vertex.ofFin j ∉ (activeSet θ).activeCols) :
    givensProduct θ i j = 0 := by
  rw [ActiveSet.mem_activeCols_iff] at hC
  push Not at hC
  obtain ⟨hnotactive, hjne_n⟩ := hC
  have h_value : (Vertex.ofFin j).value = j.val + 1 := rfl
  have hjne : j.val + 1 ≠ n := h_value ▸ hjne_n
  have hjbound : j.val < n - 1 := by have := j.isLt; omega
  have hcos0 : Real.cos (θ ⟨j.val, hjbound⟩) = 0 := by
    by_contra hne
    let k : Vertex (n - 1) := Vertex.ofFin ⟨j.val, hjbound⟩
    have hkS : k ∈ (activeSet θ).elements := by
      unfold activeSet
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨j.val, hjbound⟩, hne, rfl⟩
    exact hnotactive k hkS rfl
  unfold Matrix.givensProduct
  suffices key : ∀ m (hm : m ≤ n - 1), m ≥ j.val + 1 → ∀ row : Fin n, row.val ≤ j.val →
      (List.ofFn (fun t : Fin m => givensRotation n ⟨t, by omega⟩ (θ ⟨t, by omega⟩))).prod
        row j = 0 by
    exact key (n - 1) le_rfl (by omega) i hij
  intro m
  induction m with
  | zero => intro _ hge; omega
  | succ m ih =>
    intro hm hge row hrow
    rw [partialGivensProduct_succ_eq θ m hm, Matrix.mul_apply]
    by_cases hmeq : m + 1 = j.val + 1
    · have hmeqj : m = j.val := by omega
      apply Finset.sum_eq_zero
      intro x _
      by_cases hxeqj : x = j
      · have hGjj : givensRotation n ⟨m, by omega⟩ (θ ⟨m, by omega⟩) x j = 0 := by
          unfold givensRotation
          simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
          have hk0_eq_x : (⟨m, by omega⟩ : Fin n) = x := by ext; simp; omega
          have hk0_eq_j : (⟨m, by omega⟩ : Fin n) = j := by ext; simp; omega
          have hθeq : θ ⟨m, by omega⟩ = θ ⟨j.val, hjbound⟩ := by congr 1; ext; simp; omega
          have hj_ne_m1 : j ≠ (⟨m + 1, by omega⟩ : Fin n) := by
            intro h; simp [Fin.ext_iff] at h; omega
          simp [hk0_eq_x, hxeqj, eq_comm, hθeq, hcos0, hj_ne_m1]
        rw [hGjj, mul_zero]
      · by_cases hxeqj1 : x.val = j.val + 1
        · have hPcol : (List.ofFn (fun t : Fin m =>
              givensRotation n ⟨↑t, by omega⟩ (θ ⟨↑t, by omega⟩))).prod row x = 0 := by
            rw [partialGivensProduct_apply_of_col_ge θ m (by omega) x (by omega) row]
            simp only [ite_eq_right_iff, one_ne_zero]
            intro h; simp [Fin.ext_iff] at h; omega
          rw [hPcol, zero_mul]
        · have hGid : givensRotation n ⟨m, by omega⟩ (θ ⟨m, by omega⟩) x j = 0 := by
            rw [givensRotation.apply_of_ne_row ⟨m, by omega⟩ _ x j
                  (by simp; omega) (by simp; omega),
                if_neg hxeqj]
          rw [hGid, mul_zero]
    · have hGid : ∀ x, givensRotation n ⟨m, by omega⟩ (θ ⟨m, by omega⟩) x j =
          if x = j then 1 else 0 := fun x =>
        givensRotation.apply_of_ne_col ⟨m, by omega⟩ _ x j (by simp; omega) (by simp; omega)
      simp_rw [hGid, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      exact ih (by omega) (by omega) row hrow

end HessenbergDigraphs
