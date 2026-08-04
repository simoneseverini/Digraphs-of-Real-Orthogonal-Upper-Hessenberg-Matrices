/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Vertex
import HessenbergDigraphs.ActiveSet
import HessenbergDigraphs.Combinatorial.Degree

/-!
# Cut lemma and structural in-degree facts (bundled-structure form)
-/

namespace HessenbergDigraphs

open Finset Nat

variable {n : ℕ} (S : ActiveSet n)

/-! ## Mathematical layer — backward arcs are spine arcs. -/

/-- **Math.** An arc `(i, j)` with `j.value < i.value` is a spine arc. -/
theorem backward_arc_is_spine (i j : Vertex n)
    (harc : Arc S i j) (hij : j.value < i.value) :
    ∃ h : j.value < n, i = j.next h := by
  rcases (arc_iff_spine_or_overlay S i j).mp harc with ⟨h, hi_eq⟩ | ⟨_, _, hij'⟩
  · exact ⟨h, hi_eq⟩
  · exfalso
    have : i.value ≤ j.value := hij'
    omega

/-! ## Mathematical layer — cut lemma. -/

/-- **Math.** The only arc of `D_n(S)` crossing the cut from `{k+1, …, n}` down
to `{1, …, k}` is the spine arc `(k+1, k)`. -/
theorem cut_lemma (k : ℕ) (i j : Vertex n)
    (harc : Arc S i j) (hi : k + 1 ≤ i.value) (hj : j.value ≤ k) :
    i.value = k + 1 ∧ j.value = k := by
  rcases (arc_iff_spine_or_overlay S i j).mp harc with ⟨_, hi_eq⟩ | ⟨_, _, hij⟩
  · have h_value := congrArg Vertex.value hi_eq
    simp at h_value
    omega
  · exfalso
    have : i.value ≤ j.value := hij
    omega

/-! ## Mathematical layer — Paper Proposition 9 (interior `j`). -/

/-- **Math.** For `j` corresponding to an element of `S`, the in-degree of `j`
in `D_n(S)` equals `2 + |elements with value < j.value|`. -/
theorem inDeg_mem_S (j : Vertex n) (hn : 2 ≤ n)
    (hjS : ∃ k ∈ S.elements, k.value = j.value) :
    inDeg S j = 1 + ((S.elements.filter (fun k => k.value < j.value)).card + 1) := by
  obtain ⟨k0, hk0S, hk0_eq⟩ := hjS
  have hj_pos : 1 ≤ j.value := j.one_le_value
  have hj_lt : j.value < n := by have := k0.value_le_n; omega
  have hn1 : 1 ≤ n := by omega
  -- Witness vertices for the partition
  set j_succ : Vertex n := j.next hj_lt with hjs_def
  set v_first : Vertex n := Vertex.first hn1 with hvf_def
  let f : Vertex (n - 1) → Vertex n :=
    fun k => ⟨k.value + 1,
              by have := k.one_le_value; omega,
              by have := k.value_le_n; omega⟩
  set target_image : Finset (Vertex n) :=
    (S.elements.filter (fun k => k.value < j.value)).image f with htgt_def
  -- The filter equals `insert j_succ (insert v_first target_image)`
  have h_split : (Finset.univ : Finset (Vertex n)).filter (fun i => Arc S i j) =
                 insert j_succ (insert v_first target_image) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_insert]
    constructor
    · intro harc
      rcases (arc_iff_spine_or_overlay S i j).mp harc with ⟨h_lt, hi_eq⟩ | ⟨hi, _, hij⟩
      · left
        ext
        show i.value = j_succ.value
        have := congrArg Vertex.value hi_eq
        simp only [Vertex.next_value] at this
        change i.value = j.value + 1
        exact this
      · rcases (ActiveSet.mem_activeRows_iff S i).mp hi with hi_first | ⟨k, hkS, hk_eq⟩
        · right; left
          ext
          show i.value = v_first.value
          change i.value = 1
          exact hi_first
        · right; right
          rw [htgt_def, Finset.mem_image]
          refine ⟨k, ?_, ?_⟩
          · rw [Finset.mem_filter]
            refine ⟨hkS, ?_⟩
            have h_le : i.value ≤ j.value := hij
            omega
          · ext; change k.value + 1 = i.value; exact hk_eq
    · rintro (h_eq | h_eq | h_image)
      · rw [h_eq]
        exact Arc.spine j hj_lt
      · rw [h_eq]
        refine Arc.overlay _ _ (ActiveSet.first_mem_activeRows hn1 S) ?_ ?_
        · rw [ActiveSet.mem_activeCols_iff]; left
          exact ⟨k0, hk0S, hk0_eq⟩
        · change v_first.value ≤ j.value
          change 1 ≤ j.value
          exact hj_pos
      · rw [htgt_def, Finset.mem_image] at h_image
        obtain ⟨k, hk_filter, hk_eq⟩ := h_image
        rw [Finset.mem_filter] at hk_filter
        obtain ⟨hkS, hk_lt⟩ := hk_filter
        rw [← hk_eq]
        refine Arc.overlay _ _ ?_ ?_ ?_
        · rw [ActiveSet.mem_activeRows_iff]; right
          exact ⟨k, hkS, rfl⟩
        · rw [ActiveSet.mem_activeCols_iff]; left
          exact ⟨k0, hk0S, hk0_eq⟩
        · change k.value + 1 ≤ j.value
          omega
  -- Now compute cardinality
  have hf_inj : Function.Injective f := by
    intro a b hab
    ext
    have h_value := congrArg Vertex.value hab
    have : a.value + 1 = b.value + 1 := h_value
    omega
  have h1 : v_first ∉ target_image := by
    rw [htgt_def, Finset.mem_image]
    rintro ⟨k, hk_filter, hk_eq⟩
    rw [Finset.mem_filter] at hk_filter
    obtain ⟨_, _⟩ := hk_filter
    have h_value := congrArg Vertex.value hk_eq
    have : k.value + 1 = 1 := h_value
    have := k.one_le_value
    omega
  have h2 : j_succ ∉ insert v_first target_image := by
    rw [Finset.mem_insert]
    rintro (h_eq | h_image)
    · have h_value := congrArg Vertex.value h_eq
      have : j.value + 1 = 1 := h_value
      omega
    · rw [htgt_def, Finset.mem_image] at h_image
      obtain ⟨k, hk_filter, hk_eq⟩ := h_image
      rw [Finset.mem_filter] at hk_filter
      obtain ⟨_, hk_lt⟩ := hk_filter
      have h_value := congrArg Vertex.value hk_eq
      have : k.value + 1 = j.value + 1 := h_value
      omega
  unfold inDeg
  rw [h_split, Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1,
      Finset.card_image_of_injective _ hf_inj]
  omega

end HessenbergDigraphs
