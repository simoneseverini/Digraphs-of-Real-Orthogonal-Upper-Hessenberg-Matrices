/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Vertex
import HessenbergDigraphs.ActiveSet
import HessenbergDigraphs.Combinatorial.Arc

/-!
# Loop characterization for `D_n(S)` (bundled-structure form)

Loops in `D_n(S)` occur exactly at vertices that lie in both
`S.activeRows` and `S.activeCols`. The closed-form characterisation
splits into three cases by vertex location, and the loopless variant
is captured by `S ⊆ {2, …, n - 2}` together with no-consecutive.

## Main results

* `loop_iff_mem_activeRows_and_activeCols` (Paper: Lemma 13).
* `loop_at_first`, `loop_at_last`, `loop_at_mid` — boundary regimes.
* `loopless_iff` — Paper: Corollary 14.

## References

Severini — Lemma 13 and Corollary 14.
-/

namespace HessenbergDigraphs

open Finset Nat

variable {n : ℕ} (S : ActiveSet n)

/-! ## Mathematical layer — Paper: Lemma 13 (loop characterisation, all `v`). -/

/-- **Math.** `D_n(S)` has a loop at vertex `v` iff `v` is in both the active row set
and the active column set. Paper: Lemma 13. The spine constructor cannot
fire on `Arc S v v` (it would require `v = v.next h`, contradicting
`v.value ≠ v.value + 1`). -/
theorem loop_iff_mem_activeRows_and_activeCols (v : Vertex n) :
    Loop S v ↔ v ∈ S.activeRows ∧ v ∈ S.activeCols := by
  refine ⟨fun h => ?_, fun ⟨hi, hj⟩ => loop_of_mem hi hj⟩
  rcases (arc_iff_spine_or_overlay S v v).mp h with ⟨h_lt, hv_eq⟩ | ⟨hi, hj, _⟩
  · exfalso
    have key := congrArg Vertex.value hv_eq
    simp at key
  · exact ⟨hi, hj⟩

/-! ## Mathematical layer — Paper: Lemma 13 (case `v = first`). -/

/-- **Math.** A loop at vertex `1` exists iff `1 ∈ S` (i.e. some element of
`S.elements` has value `1`). Paper: Lemma 13 (case `v = 1`). -/
theorem loop_at_first (hn : 2 ≤ n) :
    Loop S (Vertex.first (by omega : 1 ≤ n)) ↔
    ∃ k ∈ S.elements, k.value = 1 := by
  rw [loop_iff_mem_activeRows_and_activeCols]
  constructor
  · rintro ⟨_, hj⟩
    rcases (ActiveSet.mem_activeCols_iff S _).mp hj with ⟨k, hkS, hk_eq⟩ | hn1
    · refine ⟨k, hkS, ?_⟩
      have : (Vertex.first (by omega : 1 ≤ n)).value = 1 := rfl
      omega
    · -- hn1 : (Vertex.first _).value = n; but (Vertex.first _).value = 1.
      have : (Vertex.first (by omega : 1 ≤ n)).value = 1 := rfl
      omega
  · rintro ⟨k, hkS, hk_eq⟩
    refine ⟨ActiveSet.first_mem_activeRows _ S, ?_⟩
    rw [ActiveSet.mem_activeCols_iff]
    left
    refine ⟨k, hkS, ?_⟩
    have : (Vertex.first (by omega : 1 ≤ n)).value = 1 := rfl
    omega

/-! ## Mathematical layer — Paper: Lemma 13 (case `v = last`). -/

/-- **Math.** A loop at vertex `n` exists iff `n - 1 ∈ S` (i.e. some element of
`S.elements` has value `n - 1`). Paper: Lemma 13 (case `v = n`). -/
theorem loop_at_last (hn : 2 ≤ n) :
    Loop S (Vertex.last (by omega : 1 ≤ n)) ↔
    ∃ k ∈ S.elements, k.value = n - 1 := by
  rw [loop_iff_mem_activeRows_and_activeCols]
  constructor
  · rintro ⟨hi, _⟩
    rcases (ActiveSet.mem_activeRows_iff S _).mp hi with h_eq | ⟨k, hkS, hk_eq⟩
    · -- (Vertex.last _).value = n, but h_eq says it equals 1
      simp only [Vertex.last] at h_eq
      omega
    · refine ⟨k, hkS, ?_⟩
      have : k.value + 1 = n := by
        have hlast : (Vertex.last (by omega : 1 ≤ n)).value = n := rfl
        rw [hlast] at hk_eq
        exact hk_eq
      omega
  · rintro ⟨k, hkS, hk_eq⟩
    refine ⟨?_, ActiveSet.last_mem_activeCols _ S⟩
    rw [ActiveSet.mem_activeRows_iff]
    right
    refine ⟨k, hkS, ?_⟩
    change k.value + 1 = (Vertex.last (by omega : 1 ≤ n)).value
    change k.value + 1 = n
    omega

/-! ## Mathematical layer — Paper: Lemma 13 (interior case). -/

/-- **Math.** A loop at an interior vertex `v` (with `2 ≤ v.value ≤ n - 1`) exists
iff both `v.value - 1` and `v.value` are values of elements of `S`. -/
theorem loop_at_mid (v : Vertex n) (hv1 : 2 ≤ v.value) (hv2 : v.value ≤ n - 1) :
    Loop S v ↔
    (∃ k ∈ S.elements, k.value = v.value - 1) ∧
    (∃ k ∈ S.elements, k.value = v.value) := by
  rw [loop_iff_mem_activeRows_and_activeCols]
  constructor
  · rintro ⟨hi, hj⟩
    refine ⟨?_, ?_⟩
    · rcases (ActiveSet.mem_activeRows_iff S v).mp hi with h_eq | ⟨k, hkS, hk_eq⟩
      · omega
      · exact ⟨k, hkS, by omega⟩
    · rcases (ActiveSet.mem_activeCols_iff S v).mp hj with ⟨k, hkS, hk_eq⟩ | h_eq
      · exact ⟨k, hkS, hk_eq⟩
      · omega
  · rintro ⟨⟨kp, hkpS, hkp_eq⟩, ⟨kv, hkvS, hkv_eq⟩⟩
    refine ⟨?_, ?_⟩
    · rw [ActiveSet.mem_activeRows_iff]
      right; exact ⟨kp, hkpS, by omega⟩
    · rw [ActiveSet.mem_activeCols_iff]
      left; exact ⟨kv, hkvS, hkv_eq⟩

/-! ## Mathematical layer — Paper: Corollary 14 (loopless characterisation). -/

/-- **Math.** `D_n(S)` is loopless iff no element of `S.elements` has value `1` or
`n - 1`, and no two elements are consecutive. Paper: Corollary 14. -/
theorem loopless_iff (hn : 3 ≤ n) :
    (∀ v : Vertex n, ¬Loop S v) ↔
    ((∀ k ∈ S.elements, 2 ≤ k.value ∧ k.value ≤ n - 2) ∧ NoConsecutive S) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro k hk
      refine ⟨?_, ?_⟩
      · by_contra hkLt
        push Not at hkLt
        have hk1 : k.value = 1 := by have := k.one_le_value; omega
        exact h _ ((loop_at_first S (by omega)).mpr ⟨k, hk, hk1⟩)
      · by_contra hkGt
        push Not at hkGt
        have hkEq : k.value = n - 1 := by have := k.value_le_n; omega
        exact h _ ((loop_at_last S (by omega)).mpr ⟨k, hk, hkEq⟩)
    · intro k k' hk hk' hkk'
      -- k.value + 1 = k'.value, derive contradiction via loop at v = k'.value
      -- Need v : Vertex n with v.value = k'.value (interior since 2 ≤ k'.value ≤ n - 1)
      have hk_pos : 1 ≤ k.value := k.one_le_value
      have hk_le : k.value ≤ n - 1 := by have := k.value_le_n; omega
      have hk'_pos : 1 ≤ k'.value := k'.one_le_value
      have hk'_le : k'.value ≤ n - 1 := by have := k'.value_le_n; omega
      have hv2 : 2 ≤ k'.value := by omega
      have hvn1 : k'.value ≤ n - 1 := hk'_le
      let v : Vertex n :=
        ⟨k'.value, k'.one_le_value, by have := k'.value_le_n; omega⟩
      apply h v
      apply (loop_at_mid S v hv2 hvn1).mpr
      refine ⟨⟨k, hk, ?_⟩, ⟨k', hk', rfl⟩⟩
      show k.value = v.value - 1
      change k.value = k'.value - 1
      omega
  · rintro ⟨hRange, hNC⟩ v hLoop
    rcases (loop_iff_mem_activeRows_and_activeCols S v).mp hLoop with ⟨hi, hj⟩
    -- Three cases by v.value: = 1, = n, interior
    by_cases hv_eq_1 : v.value = 1
    · -- v.value = 1 case
      have h1S : ∃ k ∈ S.elements, k.value = 1 :=
        (loop_at_first S (by omega)).mp <| by
          rw [show v = Vertex.first (by omega : 1 ≤ n) from by ext; exact hv_eq_1] at hLoop
          exact hLoop
      obtain ⟨k, hkS, hk1⟩ := h1S
      have ⟨h1ge, _⟩ := hRange k hkS
      omega
    · by_cases hv_eq_n : v.value = n
      · -- v.value = n case
        have hn1S : ∃ k ∈ S.elements, k.value = n - 1 :=
          (loop_at_last S (by omega)).mp <| by
            rw [show v = Vertex.last (by omega : 1 ≤ n) from by ext; exact hv_eq_n] at hLoop
            exact hLoop
        obtain ⟨k, hkS, hkn1⟩ := hn1S
        have ⟨_, hn1le⟩ := hRange k hkS
        omega
      · -- interior case
        have hv2 : 2 ≤ v.value := by have := v.one_le_value; omega
        have hvn1 : v.value ≤ n - 1 := by have := v.value_le_n; omega
        obtain ⟨⟨kp, hkpS, hkp_eq⟩, ⟨kv, hkvS, hkv_eq⟩⟩ :=
          (loop_at_mid S v hv2 hvn1).mp hLoop
        exact hNC kp kv hkpS hkvS (by omega)

end HessenbergDigraphs
