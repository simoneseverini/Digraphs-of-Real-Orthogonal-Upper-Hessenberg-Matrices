/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import HessenbergDigraphs.Vertex
import HessenbergDigraphs.ActiveSet
import HessenbergDigraphs.Combinatorial.Arc
import HessenbergDigraphs.Matrix.UnreducedAngles
import HessenbergDigraphs.Realization.Vanishing
import HessenbergDigraphs.Realization.Propagation

/-!
# Digraph model: support of `givensProduct` equals `D_n(activeSet θ)` (bundled-structure form)
-/

namespace HessenbergDigraphs

open Matrix Finset

variable {n : ℕ}

/-- **Mixed.** Upper-triangular entries of `givensProduct θ` are non-zero iff the
overlay arc condition holds. -/
theorem givensProduct_upper_ne_zero_iff
    (θ : Fin (n - 1) → ℝ) (hunred : ∀ k : Fin (n - 1), Real.sin (θ k) ≠ 0)
    (i j : Fin n) (hij : (i : ℕ) ≤ (j : ℕ)) :
    givensProduct θ i j ≠ 0 ↔
      (Vertex.ofFin i ∈ (activeSet θ).activeRows ∧
       Vertex.ofFin j ∈ (activeSet θ).activeCols ∧
       (Vertex.ofFin i).value ≤ (Vertex.ofFin j).value) := by
  constructor
  · intro hne
    refine ⟨?_, ?_, ?_⟩
    · by_contra hR
      exact hne (givensProduct_row_vanishing θ hunred i j hij hR)
    · by_contra hC
      exact hne (givensProduct_col_vanishing θ hunred i j hij hC)
    · change i.val + 1 ≤ j.val + 1
      omega
  · intro ⟨hR, hC, _⟩
    exact givensProduct_upper_ne_zero_of_arc θ hunred i j hij hR hC

/-- **Mixed.** Bridge theorem (Fin-typed internal form): the support digraph of an
unreduced Givens product `givensProduct θ` is exactly `D_n(activeSet θ)`. -/
theorem digraph_model_fin (hn : 2 ≤ n) (θ : Fin (n - 1) → ℝ)
    (hunred : ∀ k : Fin (n - 1), Real.sin (θ k) ≠ 0) :
    ∀ i j : Fin n, givensProduct θ i j ≠ 0 ↔
      Arc (activeSet θ) (Vertex.ofFin i) (Vertex.ofFin j) := by
  intro i j
  constructor
  · intro hne
    by_cases hij : (j : ℕ) + 1 < (i : ℕ)
    · exact absurd (givensProduct_apply_below_subdiag θ i j hij) hne
    · by_cases heq : (i : ℕ) = (j : ℕ) + 1
      · -- Spine arc: i.val = j.val + 1, so Vertex.ofFin i = (Vertex.ofFin j).next h
        have hjlt : j.val + 1 < n := by have := i.isLt; omega
        have hjvalt : (Vertex.ofFin j).value < n := by
          change j.val + 1 < n
          exact hjlt
        have heqv : Vertex.ofFin i = (Vertex.ofFin j).next hjvalt := by
          ext
          change i.val + 1 = j.val + 1 + 1
          omega
        rw [heqv]
        exact Arc.spine (Vertex.ofFin j) hjvalt
      · have hle : (i : ℕ) ≤ (j : ℕ) := by omega
        obtain ⟨hR, hC, hij'⟩ :=
          (givensProduct_upper_ne_zero_iff θ hunred i j hle).mp hne
        exact Arc.overlay _ _ hR hC hij'
  · intro harc
    rcases (arc_iff_spine_or_overlay (activeSet θ) (Vertex.ofFin i) (Vertex.ofFin j)).mp harc
      with ⟨h_lt, hi_eq⟩ | ⟨hR, hC, hij⟩
    · -- spine: Vertex.ofFin i = (Vertex.ofFin j).next h_lt, i.e., i.val + 1 = j.val + 1 + 1
      have hjvalt : j.val + 1 < n := by
        have : (Vertex.ofFin j).value < n := h_lt
        change j.val + 1 < n
        exact this
      have hieq : i.val = j.val + 1 := by
        have := congrArg Vertex.value hi_eq
        simp only [Vertex.next_value] at this
        change i.val = j.val + 1
        have h_ofi : (Vertex.ofFin i).value = i.val + 1 := rfl
        have h_ofjnext : ((Vertex.ofFin j).next h_lt).value = (Vertex.ofFin j).value + 1 := rfl
        have h_ofj : (Vertex.ofFin j).value = j.val + 1 := rfl
        omega
      have hi_val : i = ⟨j.val + 1, hjvalt⟩ := Fin.ext (by simp; omega)
      rw [hi_val, givensProduct_apply_subdiag_eq_sin θ j hjvalt]
      exact hunred ⟨j.val, by omega⟩
    · -- overlay
      have hle' : (i : ℕ) ≤ (j : ℕ) := by
        have : (Vertex.ofFin i).value ≤ (Vertex.ofFin j).value := hij
        change i.val ≤ j.val
        have hi : (Vertex.ofFin i).value = i.val + 1 := rfl
        have hj : (Vertex.ofFin j).value = j.val + 1 := rfl
        omega
      exact (givensProduct_upper_ne_zero_iff θ hunred i j hle').mpr ⟨hR, hC, hij⟩

/-- **Mixed.** For every `S : ActiveSet n`, there exists an unreduced Givens parameter
`θ` with `activeSet θ = S` (Fin-typed internal form). -/
theorem completeness_fin (S : ActiveSet n) :
    ∃ θ : Fin (n - 1) → ℝ,
      (∀ k, Real.sin (θ k) ≠ 0) ∧ activeSet θ = S := by
  refine ⟨fun k =>
            if ∃ x ∈ S.elements, x.value = (k : ℕ) + 1
            then Real.pi / 4 else Real.pi / 2, ?_, ?_⟩
  · intro k
    dsimp only
    split_ifs with h
    · rw [Real.sin_pi_div_four]; positivity
    · rw [Real.sin_pi_div_two]; exact one_ne_zero
  · ext x
    -- x : Vertex (n - 1); show x ∈ activeSet θ.elements ↔ x ∈ S.elements
    unfold activeSet
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, hkx⟩
      -- hk : Real.cos ... ≠ 0 means there exists witness in S.elements with value k.val + 1
      -- after rewrite by hkx, we get x.value = k.val + 1
      split_ifs at hk with h
      · obtain ⟨y, hyS, hyv⟩ := h
        have h_xv : x.value = k.val + 1 := by
          have := congrArg Vertex.value hkx.symm
          exact this
        have h_yx : y = x := by
          ext; rw [hyv, h_xv]
        rw [← h_yx]; exact hyS
      · exfalso; exact hk (by rw [Real.cos_pi_div_two])
    · intro hxS
      refine ⟨⟨x.value - 1, by have := x.one_le_value; have := x.value_le_n; omega⟩, ?_, ?_⟩
      · have h_xv : x.value - 1 + 1 = x.value := by have := x.one_le_value; omega
        change Real.cos (if ∃ y ∈ S.elements, y.value = x.value - 1 + 1
                        then Real.pi / 4 else Real.pi / 2) ≠ 0
        rw [h_xv]
        rw [if_pos ⟨x, hxS, rfl⟩]
        rw [Real.cos_pi_div_four]
        positivity
      · ext
        change x.value - 1 + 1 = x.value
        have := x.one_le_value; omega

/-! ## Mathematical layer — bundled-structure form: bridge stated against
    `UnreducedAngles n`, `Vertex n`, and the `θ.activeSet.digraph` /
    `θ.product.apply` paper-side accessors. -/

/-- **Math.** Bridge theorem (bundled-structure form, equality form): the support
digraph of `θ.product` equals `θ.activeSet.digraph` as `Digraph n`s. -/
theorem digraph_model (hn : 2 ≤ n) (θ : UnreducedAngles n) :
    θ.product.supportDigraph = θ.activeSet.digraph := by
  funext i j
  apply propext
  change θ.product.apply i j ≠ 0 ↔ θ.activeSet.digraph i j
  have h_unred : ∀ k : Fin (n - 1), Real.sin (θ.toFinFunction k) ≠ 0 :=
    fun k => θ.is_unreduced ⟨k.val + 1, Nat.succ_le_succ (Nat.zero_le _),
      by have := k.isLt; omega⟩
  have h := digraph_model_fin hn θ.toFinFunction h_unred i.toFin j.toFin
  rw [Vertex.ofFin_toFin, Vertex.ofFin_toFin] at h
  rw [arc_iff_digraph] at h
  exact h

/-- **Math.** Realizability (bundled-structure form): every `S : ActiveSet n` is
`θ.activeSet` for some `θ : UnreducedAngles n`. -/
theorem completeness (S : ActiveSet n) :
    ∃ θ : UnreducedAngles n, θ.activeSet = S := by
  obtain ⟨f, hf_unred, hf_eq⟩ := completeness_fin S
  refine ⟨UnreducedAngles.fromFinFunction f hf_unred, ?_⟩
  change HessenbergDigraphs.activeSet (UnreducedAngles.fromFinFunction f hf_unred).toFinFunction = S
  rw [UnreducedAngles.toFinFunction_fromFinFunction]
  exact hf_eq

end HessenbergDigraphs
