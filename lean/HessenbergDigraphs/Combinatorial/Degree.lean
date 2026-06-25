/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Combinatorial.Arc
import Mathlib.Data.Finset.Card

/-!
# Degree theory for `D_n(S)` (bundled-structure form)

In- and out-degrees of vertices in `D_n(S)`, the boundary formulas at
`first` and `last`, the criterion for `k ∈ S` via the existence of an
arc from `first`, and the fact that any digraph isomorphism preserves
in-degrees.

## Main results

* `outDeg`, `inDeg` — out- and in-degree of a vertex.
* `outDeg_first` — Paper: Proposition 9.
* `inDeg_last` — Paper: Proposition 9.
* `mem_S_iff_arc_from_first`.
* `iso_preserves_inDeg`.

## References

Severini — Proposition 9.
-/

namespace HessenbergDigraphs

open Finset Nat Digraph

variable {n : ℕ} (S : ActiveSet n)

/-! ## Mathematical layer — out-degree counting (Lean-side definition). -/

/-- **Math.** Out-degree of vertex `i` in `D_n(S)`. -/
def outDeg (i : Vertex n) : ℕ :=
  ((Finset.univ : Finset (Vertex n)).filter (Arc S i)).card

/-- **Math.** In-degree of vertex `j` in `D_n(S)`. -/
def inDeg (j : Vertex n) : ℕ :=
  ((Finset.univ : Finset (Vertex n)).filter (fun i => Arc S i j)).card

/-! ## Mathematical layer — Paper Proposition 9 (case `v = first`). -/

/-- **Math.** The out-degree of vertex `1` in `D_n(S)` equals `|S| + 1`.
Paper: Proposition 9. -/
theorem outDeg_first (hn : 2 ≤ n) :
    outDeg S (Vertex.first (by omega : 1 ≤ n)) = S.elements.card + 1 := by
  unfold outDeg
  have h_filter : (Finset.univ : Finset (Vertex n)).filter
      (Arc S (Vertex.first (by omega : 1 ≤ n))) = S.activeCols := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro harc
      rcases (arc_iff_spine_or_overlay S _ j).mp harc with ⟨h_lt, hi_eq⟩ | ⟨_, hjC, _⟩
      · exfalso
        have h_value := congrArg Vertex.value hi_eq
        simp [Vertex.first] at h_value
        have := j.one_le_value
        omega
      · exact hjC
    · intro hj
      exact Arc.overlay _ _ (ActiveSet.first_mem_activeRows _ _) hj
        (by change (Vertex.first (by omega : 1 ≤ n)).value ≤ j.value
            change 1 ≤ j.value
            exact j.one_le_value)
  rw [h_filter]
  -- |S.activeCols| = S.elements.card + 1
  unfold ActiveSet.activeCols
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ ?_]
  · -- after image: card = S.elements.card; after singleton (inside if): 1
    have hn1 : 1 ≤ n := by omega
    simp [hn1]
  · -- Vertex.castGE injective
    intro a b hab
    ext
    have := congrArg Vertex.value hab
    simpa using this
  · -- disjoint
    rw [Finset.disjoint_left]
    intro x hx hxL
    have hn1 : 1 ≤ n := by omega
    simp only [hn1, Finset.mem_image, Finset.mem_singleton, dite_true] at hxL hx
    obtain ⟨k, _, hk_eq⟩ := hx
    have h_castGE : (Vertex.castGE (Nat.sub_le n 1) k).value = k.value := rfl
    have h_last : (Vertex.last hn1).value = n := rfl
    have hkv : k.value = x.value := by rw [← h_castGE]; rw [hk_eq]
    have hxv : x.value = n := by rw [hxL]; rfl
    have := k.value_le_n
    omega

/-! ## Mathematical layer — Paper Proposition 9 (case `v = last`). -/

/-- **Math.** The in-degree of vertex `n` in `D_n(S)` equals `|S| + 1`.
Paper: Proposition 9. -/
theorem inDeg_last (hn : 2 ≤ n) :
    inDeg S (Vertex.last (by omega : 1 ≤ n)) = S.elements.card + 1 := by
  unfold inDeg
  have h_filter : (Finset.univ : Finset (Vertex n)).filter
      (fun i => Arc S i (Vertex.last (by omega : 1 ≤ n))) = S.activeRows := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro harc
      rcases (arc_iff_spine_or_overlay S i _).mp harc with ⟨h_lt, _⟩ | ⟨hi, _, _⟩
      · -- spine: requires (Vertex.last _).value < n, but it equals n
        have h_last : (Vertex.last (by omega : 1 ≤ n)).value = n := rfl
        rw [h_last] at h_lt
        omega
      · exact hi
    · intro hi
      exact Arc.overlay _ _ hi (ActiveSet.last_mem_activeCols _ _)
        (by change i.value ≤ (Vertex.last (by omega : 1 ≤ n)).value
            change i.value ≤ n
            exact i.value_le_n)
  rw [h_filter]
  -- |S.activeRows| = S.elements.card + 1
  unfold ActiveSet.activeRows
  have hn1 : 1 ≤ n := by omega
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ ?_]
  · simp [hn1]; omega
  · intro a b hab
    ext
    have := congrArg Vertex.value hab
    simp only [add_left_inj] at this
    exact this
  · rw [Finset.disjoint_left]
    intro x hxL hxR
    simp only [hn1, Finset.mem_singleton, dite_true] at hxL
    simp only [Finset.mem_image] at hxR
    obtain ⟨k, _, hk_eq⟩ := hxR
    have hxv : x.value = 1 := by rw [hxL]; rfl
    have hk_value : k.value + 1 = x.value := by
      have := congrArg Vertex.value hk_eq
      simpa using this
    have := k.one_le_value
    omega

/-! ## Mathematical layer — membership ↔ arc from `first`. -/

/-- **Math.** An interior vertex `k` (with `k.value < n`) corresponds to a value
of some `S.elements` member iff there is an arc from `first` to `k`. -/
theorem mem_S_iff_arc_from_first (k : Vertex n) (hn : 2 ≤ n) (hk : k.value < n) :
    (∃ k' ∈ S.elements, k'.value = k.value) ↔
    Arc S (Vertex.first (by omega : 1 ≤ n)) k := by
  constructor
  · rintro ⟨k', hk'S, hk'_eq⟩
    refine Arc.overlay _ _ (ActiveSet.first_mem_activeRows _ _) ?_ ?_
    · rw [ActiveSet.mem_activeCols_iff]
      left; exact ⟨k', hk'S, hk'_eq⟩
    · change (Vertex.first (by omega : 1 ≤ n)).value ≤ k.value
      change 1 ≤ k.value; exact k.one_le_value
  · intro h
    rcases (arc_iff_spine_or_overlay S _ k).mp h with ⟨h_lt, hi_eq⟩ | ⟨_, hjC, _⟩
    · exfalso
      have := congrArg Vertex.value hi_eq
      simp [Vertex.first] at this
      have := k.one_le_value
      omega
    · rcases (ActiveSet.mem_activeCols_iff S k).mp hjC with ⟨k', hk'S, hk'_eq⟩ | hkn
      · exact ⟨k', hk'S, hk'_eq⟩
      · exfalso; omega

/-! ## Mixed — Math: iso preserves in-degree (standard graph fact).
    | Eng: bijection between in-arcs of `v` and in-arcs of `σ v`,
    via the iso permutation `σ : Equiv.Perm (Vertex n)`. -/

/-- **Mixed.** A digraph isomorphism `D_n(S) → D_n(S')` preserves in-degrees. -/
theorem iso_preserves_inDeg (S' : ActiveSet n) (σ : Equiv.Perm (Vertex n))
    (hσ : ∀ i j : Vertex n, Arc S i j ↔ Arc S' (σ i) (σ j)) (v : Vertex n) :
    inDeg S v = inDeg S' (σ v) := by
  refine Finset.card_bij (fun i _ => σ i) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact (hσ a v).mp ha
  · intro a₁ _ a₂ _ heq
    exact σ.injective heq
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨σ.symm b, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := (hσ (σ.symm b) v).mpr
    rw [Equiv.apply_symm_apply] at this
    exact this hb

/-! ## Mathematical layer — in-degree upper bound. The in-neighbours of `v`
    split into the unique spine predecessor `v.next` (value `v + 1`) and the
    overlay in-neighbours (value `≤ v`), which are disjoint. The map
    `i ↦ if i ∈ activeRows then i else first` injects the in-neighbours into
    `activeRows`, so `inDeg v ≤ |activeRows| = |S| + 1`. -/

/-- **Math.** Every in-degree in `D_n(S)` is at most `|S| + 1`. With `inDeg_last`
this pins the maximum in-degree of `D_n(S)` to exactly `|S| + 1`. -/
theorem inDeg_le (v : Vertex n) (hn : 1 ≤ n) :
    inDeg S v ≤ S.elements.card + 1 := by
  unfold inDeg
  rw [← S.card_activeRows hn]
  have spine_of_not_row : ∀ i : Vertex n, Arc S i v → i ∉ S.activeRows →
      ∃ h : v.value < n, i = v.next h := by
    intro i hai hir
    rcases (arc_iff_spine_or_overlay S i v).mp hai with hsp | ⟨hi, _, _⟩
    · exact hsp
    · exact absurd hi hir
  apply Finset.card_le_card_of_injOn
    (fun i => if i ∈ S.activeRows then i else Vertex.first hn)
  · intro i _
    dsimp only
    by_cases h : i ∈ S.activeRows
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact ActiveSet.first_mem_activeRows hn S
  · intro a ha b hb hfab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    change (if a ∈ S.activeRows then a else Vertex.first hn)
         = (if b ∈ S.activeRows then b else Vertex.first hn) at hfab
    by_cases hA : a ∈ S.activeRows <;> by_cases hB : b ∈ S.activeRows
    · rw [if_pos hA, if_pos hB] at hfab; exact hfab
    · exfalso
      obtain ⟨hbnlt, hb_eq⟩ := spine_of_not_row b hb hB
      rw [if_pos hA, if_neg hB] at hfab
      subst hfab
      rcases (arc_iff_spine_or_overlay S _ v).mp ha with ⟨_, hsp⟩ | ⟨_, hvC, _⟩
      · have hval := congrArg Vertex.value hsp
        rw [Vertex.next_value] at hval
        have h1 : (Vertex.first hn).value = 1 := rfl
        have h2 := v.one_le_value
        omega
      · exact hB (by rw [hb_eq]; exact S.next_mem_activeRows v hvC hbnlt)
    · exfalso
      obtain ⟨hanlt, ha_eq⟩ := spine_of_not_row a ha hA
      rw [if_neg hA, if_pos hB] at hfab
      subst hfab
      rcases (arc_iff_spine_or_overlay S _ v).mp hb with ⟨_, hsp⟩ | ⟨_, hvC, _⟩
      · have hval := congrArg Vertex.value hsp
        rw [Vertex.next_value] at hval
        have h1 : (Vertex.first hn).value = 1 := rfl
        have h2 := v.one_le_value
        omega
      · exact hA (by rw [ha_eq]; exact S.next_mem_activeRows v hvC hanlt)
    · obtain ⟨_, ha_eq⟩ := spine_of_not_row a ha hA
      obtain ⟨_, hb_eq⟩ := spine_of_not_row b hb hB
      rw [ha_eq, hb_eq]

/-! ## Mathematical layer — `|S|` is an isomorphism invariant of `D_n(S)`,
    via the maximum in-degree `|S| + 1`. This separates the empty, singleton,
    and `|S| ≥ 2` strata in the class count. -/

/-- **Eng.** One direction of the cardinality invariant: an arc-relation
isomorphism `σ : D_n(S) → D_n(S')` gives `|S| + 1 ≤ |S'| + 1`, by transporting
the maximum-in-degree vertex `n`. -/
private theorem card_succ_le_of_iso (S' : ActiveSet n) (hn : 2 ≤ n)
    (σ : Equiv.Perm (Vertex n))
    (hσ : ∀ i j : Vertex n, Arc S i j ↔ Arc S' (σ i) (σ j)) :
    S.elements.card + 1 ≤ S'.elements.card + 1 := by
  have hn1 : 1 ≤ n := by omega
  set w := Vertex.last hn1 with hw
  have hlast : inDeg S w = S.elements.card + 1 := inDeg_last S hn
  have htrans : inDeg S w = inDeg S' (σ w) := iso_preserves_inDeg S S' σ hσ w
  have hle : inDeg S' (σ w) ≤ S'.elements.card + 1 := inDeg_le S' (σ w) hn1
  omega

/-- **Math.** A digraph isomorphism `D_n(S) ≅ D_n(S')` forces `|S| = |S'|`. The
maximum in-degree `|S| + 1` (attained at vertex `n` by `inDeg_last`, bounded by
`inDeg_le`) is an isomorphism invariant — the cross-stratum separator behind the
classification count. -/
theorem iso_card_eq (S' : ActiveSet n) (hn : 2 ≤ n)
    (hiso : S.digraph ≅ S'.digraph) :
    S.elements.card = S'.elements.card := by
  obtain ⟨σRel⟩ := hiso
  set σ : Equiv.Perm (Vertex n) := σRel.toEquiv
  have hσ : ∀ i j : Vertex n, Arc S i j ↔ Arc S' (σ i) (σ j) := by
    intro i j
    rw [arc_iff_digraph, arc_iff_digraph]
    exact σRel.map_rel_iff'.symm
  have hσ_inv : ∀ i j : Vertex n, Arc S' i j ↔ Arc S (σ.symm i) (σ.symm j) := by
    intro i j
    have h := hσ (σ.symm i) (σ.symm j)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h.symm
  have h1 := card_succ_le_of_iso S S' hn σ hσ
  have h2 := card_succ_le_of_iso S' S hn σ.symm hσ_inv
  omega

end HessenbergDigraphs
