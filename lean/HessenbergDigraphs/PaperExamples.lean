/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import HessenbergDigraphs.Matrix.UnreducedAngles
import HessenbergDigraphs.ActiveSet

/-!
# Concrete 5 × 5 instances illustrating the classification

This file packages two paper-side example digraphs as Lean
`UnreducedAngles 5` instances, with their active sets verified.
The paper exhibits these as Examples in Section~\ref{sec:results}; the
declarations here are the ground truth those examples cite.

## Main definitions

* `example_D6_S24` — the canonical Givens product on `n = 6` whose active
  set is `{2, 4}`, exhibited in the paper's Figures 2–3 (anatomy of
  `D_6({2, 4})`). Angle vector: `θ_1 = θ_3 = π/4`, others `π/2`.
* `example_D5_S2` — the canonical Givens product on `n = 5` whose active
  set is `{2}`. Angle vector: `θ_0 = θ_2 = θ_3 = π/2`, `θ_1 = π/4`.
* `example_D5_S13` — the canonical Givens product on `n = 5` whose active
  set is `{1, 3}`. Angle vector: `θ_0 = θ_2 = π/4`, `θ_1 = θ_3 = π/2`.

## Main results

* `example_D6_S24_activeSet`, `example_D5_S2_activeSet`,
  `example_D5_S13_activeSet` — the active set of each example matches the
  combinatorial subset claimed by the paper.

## References

Severini & Li, *Automation of routine mathematics: a case study* —
Examples 5.1 and 5.2 (paper Section~\ref{sec:results}).
-/

namespace HessenbergDigraphs

open Real

section ExampleD6S24

/-! ## Example — `n = 6`, `S = {2, 4}` (paper Figures 2–3) -/

/-- **Math.** Angle vector for the `D_6({2, 4})` example: `θ_1 = θ_3 = π/4`, all other
`θ_k = π/2`. The non-zero cosines fall at `k ∈ {1, 3}`, producing the
active set `{2, 4}` (since `S = {k+1 : cos θ_k ≠ 0}`). -/
noncomputable def angles_D6_S24 : Fin 5 → ℝ :=
  fun k => if k.val % 2 = 1 then Real.pi / 4 else Real.pi / 2

/-- **Math.** The angle vector for `D_6({2, 4})` is unreduced. -/
theorem angles_D6_S24_unreduced :
    ∀ k : Fin 5, Real.sin (angles_D6_S24 k) ≠ 0 := by
  intro k
  unfold angles_D6_S24
  by_cases h : k.val % 2 = 1
  · rw [if_pos h, Real.sin_pi_div_four]
    positivity
  · rw [if_neg h, Real.sin_pi_div_two]
    norm_num

/-- **Math.** The bundled `UnreducedAngles 6` for the `D_6({2, 4})` example. -/
noncomputable def example_D6_S24 : UnreducedAngles 6 :=
  UnreducedAngles.fromFinFunction angles_D6_S24 angles_D6_S24_unreduced

/-- **Math.** The active set of the `D_6({2, 4})` example is exactly `{2, 4}`: a
vertex `v ∈ {1, …, 5}` lies in the active set iff `v.value ∈ {2, 4}`. -/
theorem example_D6_S24_activeSet :
    ∀ v : Vertex 5,
      v ∈ example_D6_S24.activeSet.elements ↔ v.value = 2 ∨ v.value = 4 := by
  intro v
  unfold example_D6_S24 UnreducedAngles.activeSet
  rw [UnreducedAngles.toFinFunction_fromFinFunction]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hcos, hv⟩
    have hk : k.val % 2 = 1 := by
      by_contra hne
      apply hcos
      show Real.cos (angles_D6_S24 k) = 0
      unfold angles_D6_S24
      rw [if_neg hne]
      exact Real.cos_pi_div_two
    rw [← hv]
    change k.val + 1 = 2 ∨ k.val + 1 = 4
    have hkbound : k.val < 5 := k.isLt
    omega
  · intro hv
    rcases hv with hv | hv
    · refine ⟨⟨1, by omega⟩, ?_, ?_⟩
      · change Real.cos (angles_D6_S24 ⟨1, by omega⟩) ≠ 0
        unfold angles_D6_S24
        rw [if_pos (by decide : (1 : ℕ) % 2 = 1), Real.cos_pi_div_four]
        positivity
      · ext; change 1 + 1 = v.value; omega
    · refine ⟨⟨3, by omega⟩, ?_, ?_⟩
      · change Real.cos (angles_D6_S24 ⟨3, by omega⟩) ≠ 0
        unfold angles_D6_S24
        rw [if_pos (by decide : (3 : ℕ) % 2 = 1), Real.cos_pi_div_four]
        positivity
      · ext; change 3 + 1 = v.value; omega

end ExampleD6S24

section ExampleD5S2

/-! ## Example — `n = 5`, `S = {2}` (paper Example~\ref{ex:D5S2}) -/

/-- **Math.** Angle vector for the `D_5({2})` example: `θ_1 = π/4`, all other
`θ_k = π/2`. The single non-zero `cos` falls at index `k = 1`,
producing the active set `{2}` (since `S = {k+1 : cos θ_k ≠ 0}`). -/
noncomputable def angles_D5_S2 : Fin 4 → ℝ :=
  fun k => if k.val = 1 then Real.pi / 4 else Real.pi / 2

/-- **Math.** The angle vector for `D_5({2})` is unreduced: every sine is non-zero. -/
theorem angles_D5_S2_unreduced :
    ∀ k : Fin 4, Real.sin (angles_D5_S2 k) ≠ 0 := by
  intro k
  unfold angles_D5_S2
  by_cases h : k.val = 1
  · rw [if_pos h, Real.sin_pi_div_four]
    positivity
  · rw [if_neg h, Real.sin_pi_div_two]
    norm_num

/-- **Math.** The bundled `UnreducedAngles 5` for the `D_5({2})` example. -/
noncomputable def example_D5_S2 : UnreducedAngles 5 :=
  UnreducedAngles.fromFinFunction angles_D5_S2 angles_D5_S2_unreduced

/-- **Math.** The active set of the `D_5({2})` example is exactly `{2}` (as a finset
of `Vertex 4`): a vertex `v` lies in the active set iff `v.value = 2`. -/
theorem example_D5_S2_activeSet :
    ∀ v : Vertex 4, v ∈ example_D5_S2.activeSet.elements ↔ v.value = 2 := by
  intro v
  unfold example_D5_S2 UnreducedAngles.activeSet
  rw [UnreducedAngles.toFinFunction_fromFinFunction]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hcos, hv⟩
    have hk : k.val = 1 := by
      by_contra hne
      apply hcos
      show Real.cos (angles_D5_S2 k) = 0
      unfold angles_D5_S2
      rw [if_neg hne]
      exact Real.cos_pi_div_two
    rw [← hv]
    change k.val + 1 = 2
    omega
  · intro hv
    refine ⟨⟨1, by omega⟩, ?_, ?_⟩
    · change Real.cos (angles_D5_S2 ⟨1, by omega⟩) ≠ 0
      unfold angles_D5_S2
      rw [if_pos rfl, Real.cos_pi_div_four]
      positivity
    · ext; change 1 + 1 = v.value; omega

end ExampleD5S2

section ExampleD5S13

/-! ## Example — `n = 5`, `S = {1, 3}` -/

/-- **Math.** Angle vector for the `D_5({1, 3})` example: `θ_0 = θ_2 = π/4`,
`θ_1 = θ_3 = π/2`. The non-zero `cos` falls at indices `k ∈ {0, 2}`,
producing the active set `{1, 3}`. -/
noncomputable def angles_D5_S13 : Fin 4 → ℝ :=
  fun k => if k.val % 2 = 0 then Real.pi / 4 else Real.pi / 2

/-- **Math.** The angle vector for `D_5({1, 3})` is unreduced: every sine is non-zero. -/
theorem angles_D5_S13_unreduced :
    ∀ k : Fin 4, Real.sin (angles_D5_S13 k) ≠ 0 := by
  intro k
  unfold angles_D5_S13
  by_cases h : k.val % 2 = 0
  · rw [if_pos h, Real.sin_pi_div_four]
    positivity
  · rw [if_neg h, Real.sin_pi_div_two]
    norm_num

/-- **Math.** The bundled `UnreducedAngles 5` for the `D_5({1, 3})` example. -/
noncomputable def example_D5_S13 : UnreducedAngles 5 :=
  UnreducedAngles.fromFinFunction angles_D5_S13 angles_D5_S13_unreduced

/-- **Math.** The active set of the `D_5({1, 3})` example is exactly `{1, 3}` (as a
finset of `Vertex 4`): a vertex `v` lies in the active set iff
`v.value ∈ {1, 3}`. -/
theorem example_D5_S13_activeSet :
    ∀ v : Vertex 4,
      v ∈ example_D5_S13.activeSet.elements ↔ v.value = 1 ∨ v.value = 3 := by
  intro v
  unfold example_D5_S13 UnreducedAngles.activeSet
  rw [UnreducedAngles.toFinFunction_fromFinFunction]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hcos, hv⟩
    have hk : k.val % 2 = 0 := by
      by_contra hne
      apply hcos
      show Real.cos (angles_D5_S13 k) = 0
      unfold angles_D5_S13
      rw [if_neg hne]
      exact Real.cos_pi_div_two
    rw [← hv]
    change k.val + 1 = 1 ∨ k.val + 1 = 3
    have hkbound : k.val < 4 := k.isLt
    omega
  · intro hv
    rcases hv with hv | hv
    · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
      · change Real.cos (angles_D5_S13 ⟨0, by omega⟩) ≠ 0
        unfold angles_D5_S13
        rw [if_pos (by decide : (0 : ℕ) % 2 = 0), Real.cos_pi_div_four]
        positivity
      · ext; change 0 + 1 = v.value; omega
    · refine ⟨⟨2, by omega⟩, ?_, ?_⟩
      · change Real.cos (angles_D5_S13 ⟨2, by omega⟩) ≠ 0
        unfold angles_D5_S13
        rw [if_pos (by decide : (2 : ℕ) % 2 = 0), Real.cos_pi_div_four]
        positivity
      · ext; change 2 + 1 = v.value; omega

end ExampleD5S13

end HessenbergDigraphs
