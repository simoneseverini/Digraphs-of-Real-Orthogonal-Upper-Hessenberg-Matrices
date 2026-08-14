/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Combinatorial.Rigidity
import HessenbergDigraphs.Combinatorial.Singleton.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# Singleton-set isomorphism `D_n({t}) ≅ D_n({n - t})` (bundled-structure form)
-/

namespace HessenbergDigraphs

open Finset Nat Digraph

/-! ## Mathematical layer — Paper: Lemma 11 witness, Vertex-typed. -/

/-- **Math.** The cyclic shift `σ_t : Vertex n → Vertex n` defined by
    `σ_t(v) = ((v.value - 1 + n - t) mod n) + 1`. Paper's 1-indexed
    rotation that exhibits `D_n({t}) ≅ D_n({n - t})`. -/
def cyclicShift (n t : ℕ) (hn : 2 ≤ n) (_ht : 1 ≤ t) (_htn : t ≤ n - 1) :
    Vertex n → Vertex n :=
  fun v => Vertex.ofFin (cyclicShiftFin n t hn v.toFin)

/-- **Math.** The cyclic shift `σ_t` is injective on `Vertex n`. -/
theorem cyclic_shift_injective (n t : ℕ) (hn : 2 ≤ n) (ht : 1 ≤ t) (htn : t ≤ n - 1) :
    Function.Injective (cyclicShift n t hn ht htn) := by
  intro v₁ v₂ h
  have h_fin : cyclicShiftFin n t hn v₁.toFin = cyclicShiftFin n t hn v₂.toFin := by
    have := congrArg Vertex.toFin h
    rw [show (cyclicShift n t hn ht htn v₁).toFin =
            cyclicShiftFin n t hn v₁.toFin from Vertex.toFin_ofFin _,
        show (cyclicShift n t hn ht htn v₂).toFin =
            cyclicShiftFin n t hn v₂.toFin from Vertex.toFin_ofFin _] at this
    exact this
  have h_toFin := cyclicShiftFin_injective n t hn ht htn h_fin
  have := congrArg Vertex.ofFin h_toFin
  rw [Vertex.ofFin_toFin, Vertex.ofFin_toFin] at this
  exact this

/-- **Math.** The cyclic shift `σ_t` is a bijection on `Vertex n`. -/
theorem cyclic_shift_bijection (n t : ℕ) (hn : 2 ≤ n) (ht : 1 ≤ t) (htn : t ≤ n - 1) :
    Function.Bijective (cyclicShift n t hn ht htn) :=
  haveI : Finite (Vertex n) := Finite.intro
    (n := n) ⟨Vertex.toFin, Vertex.ofFin, Vertex.ofFin_toFin, Vertex.toFin_ofFin⟩
  ⟨cyclic_shift_injective n t hn ht htn,
   Finite.injective_iff_surjective.mp (cyclic_shift_injective n t hn ht htn)⟩

/-- **Math.** The cyclic shift packaged as an `Equiv.Perm (Vertex n)`. -/
noncomputable def cyclicShiftEquiv (n t : ℕ) (hn : 2 ≤ n) (ht : 1 ≤ t) (htn : t ≤ n - 1) :
    Equiv.Perm (Vertex n) :=
  Equiv.ofBijective (cyclicShift n t hn ht htn) (cyclic_shift_bijection n t hn ht htn)

@[simp] theorem cyclicShiftEquiv_apply (n t : ℕ) (hn : 2 ≤ n) (ht : 1 ≤ t) (htn : t ≤ n - 1)
    (v : Vertex n) :
    cyclicShiftEquiv n t hn ht htn v = cyclicShift n t hn ht htn v := rfl

/-! ## Mathematical layer — Vertex-typed wrappers for the arc preservation. -/

/-- **Math.** Forward direction of the singleton-isomorphism arc preservation,
Vertex-typed user-facing form. -/
private lemma cyclicShift_arc_forward
    (n t : ℕ) (hn : 2 ≤ n) (ht : 1 ≤ t) (htn : t ≤ n - 1) (i j : Vertex n)
    (h : Arc (singletonAs n t ht htn) i j) :
    Arc (singletonAs n (n - t) (by omega) (by omega))
        (cyclicShift n t hn ht htn i) (cyclicShift n t hn ht htn j) := by
  rw [show i = Vertex.ofFin i.toFin from (Vertex.ofFin_toFin i).symm,
      show j = Vertex.ofFin j.toFin from (Vertex.ofFin_toFin j).symm] at h
  exact cyclicShift_arc_forward_fin n t hn ht htn i.toFin j.toFin h

/-- **Math.** Backward direction of the singleton-isomorphism arc preservation,
Vertex-typed user-facing form. -/
private lemma cyclicShift_arc_backward
    (n t : ℕ) (hn : 2 ≤ n) (ht : 1 ≤ t) (htn : t ≤ n - 1) (i j : Vertex n)
    (h : Arc (singletonAs n (n - t) (by omega) (by omega))
        (cyclicShift n t hn ht htn i) (cyclicShift n t hn ht htn j)) :
    Arc (singletonAs n t ht htn) i j := by
  have h_fin := cyclicShift_arc_backward_fin n t hn ht htn i.toFin j.toFin h
  rw [Vertex.ofFin_toFin, Vertex.ofFin_toFin] at h_fin
  exact h_fin

/-! ## Mathematical layer — Paper: Lemma 11 (existence direction) -/

/-- **Math.** For any singleton active set `{t}`, the digraph `D_n({t})` is
isomorphic to `D_n({n - t})`, witnessed by the Vertex-typed cyclic shift. -/
theorem singleton_iso (n : ℕ) (t : ℕ) (hn : 2 ≤ n)
    (ht : 1 ≤ t) (htn : t ≤ n - 1) :
    (singletonAs n t ht htn).digraph ≅
    (singletonAs n (n - t) (by omega) (by omega)).digraph := by
  refine ⟨⟨cyclicShiftEquiv n t hn ht htn, ?_⟩⟩
  intro i j
  change ActiveSet.digraph _ (cyclicShift n t hn ht htn i) (cyclicShift n t hn ht htn j) ↔
       ActiveSet.digraph _ i j
  rw [← arc_iff_digraph, ← arc_iff_digraph]
  exact ⟨cyclicShift_arc_backward n t hn ht htn i j,
         cyclicShift_arc_forward n t hn ht htn i j⟩

/-! ## Mathematical layer — Lean-side characterisation of in-degree-2
    vertices in `D_n({t})`. -/

/-- **Math.** In `D_n({t})`, a vertex `v` has in-degree exactly `2` iff
    `v.value = t` or `v.value = n`. -/
theorem inDeg_eq_two_iff_singleton (n t : ℕ) (hn : 2 ≤ n) (ht : 1 ≤ t) (htn : t ≤ n - 1)
    (v : Vertex n) :
    inDeg (singletonAs n t ht htn) v = 2 ↔ v.value = t ∨ v.value = n := by
  by_cases hj : v.value = t ∨ v.value = n
  · refine ⟨fun _ => hj, fun _ => ?_⟩
    rcases hj with hvt | hvn
    · -- v.value = t: use inDeg_mem_S; filter < v is empty
      have h_inDeg := inDeg_mem_S (singletonAs n t ht htn) v hn
        ⟨⟨t, ht, htn⟩, by simp [singletonAs], hvt.symm⟩
      have h_filter_empty :
          ((singletonAs n t ht htn).elements.filter
            (fun k => k.value < v.value)).card = 0 := by
        rw [Finset.card_eq_zero]
        ext x
        simp [singletonAs]
        intro hx
        rw [hx, hvt]
      rw [h_inDeg, h_filter_empty]
    · -- v.value = n: use inDeg_last
      have h_v_eq : v = Vertex.last (by omega : 1 ≤ n) := by ext; exact hvn
      rw [h_v_eq, inDeg_last (singletonAs n t ht htn) hn]
      simp [singletonAs]
  · -- v not active-cols: inDeg = 1, so cannot equal 2
    push_neg at hj
    have hv_lt : v.value < n := by
      rcases lt_or_eq_of_le v.value_le_n with hlt | heq
      · exact hlt
      · exact absurd heq hj.2
    have hv_notC : v ∉ (singletonAs n t ht htn).activeCols := by
      rw [mem_activeCols_singleton]
      push_neg; exact hj
    have h_inDeg :=
      inDeg_eq_one_of_not_mem_activeCols (singletonAs n t ht htn) v hv_lt hv_notC
    rw [h_inDeg]
    constructor
    · intro h; omega
    · intro h_or; exact absurd h_or (not_or.mpr hj)

/-! ## Mathematical layer — Lean-side helper for Lemma 11 uniqueness;
    pinning σ at the vertex with value `t` via `h_map` + σ.injective. -/

/-- **Math.** In the non-fixing case of `singleton_iso_unique`, the helper
characterisation `h_map` together with `σ`'s injectivity pin
`σ ⟨t⟩` to `Vertex.last`. -/
private lemma sigma_maps_t_to_n_minus_1 (n t t' : ℕ) (hn : 2 ≤ n)
    (ht : 1 ≤ t) (htn : t ≤ n - 1) (_ht'n : t' ≤ n - 1)
    (σ : Equiv.Perm (Vertex n))
    (h_map : ∀ v : Vertex n, (v.value = t ∨ v.value = n) ↔
      ((σ v).value = t' ∨ (σ v).value = n))
    (h_case : ¬ σ (Vertex.last (by omega : 1 ≤ n)) = Vertex.last (by omega : 1 ≤ n)) :
    σ ⟨t, ht, by omega⟩ = Vertex.last (by omega : 1 ≤ n) := by
  set vlast := Vertex.last (by omega : 1 ≤ n) with hvlast_def
  set vt : Vertex n := ⟨t, ht, by omega⟩ with hvt_def
  -- (σ vlast).value = t' (not n, by h_case)
  have hn_eq : (σ vlast).value = t' := by
    have := (h_map vlast).mp (Or.inr rfl)
    rcases this with h | h
    · exact h
    · exfalso; apply h_case; ext; rw [h]; rfl
  -- (σ vt).value = t' or n
  have ht_cases : (σ vt).value = t' ∨ (σ vt).value = n :=
    (h_map vt).mp (Or.inl rfl)
  rcases ht_cases with h | h
  · exfalso
    have h_inj : σ vt = σ vlast := by ext; rw [h, hn_eq]
    have h_eq := σ.injective h_inj
    have h_val := congrArg Vertex.value h_eq
    have hvt_v : vt.value = t := rfl
    have hvlast_v : vlast.value = n := rfl
    rw [hvt_v, hvlast_v] at h_val
    omega
  · ext; rw [h]; rfl

/-! ## Mathematical layer — spine-arc descent step in `singleton_iso_unique`. -/

/-- **Math.** One descent step of the chain `σ ⟨t - k⟩ = ⟨n - k⟩` used in the
non-fixing case of `singleton_iso_unique`. -/
private lemma sigma_descent_step (n t t' : ℕ) (hn : 2 ≤ n)
    (ht : 1 ≤ t) (htn : t ≤ n - 1) (ht' : 1 ≤ t') (ht'n : t' ≤ n - 1)
    (σ : Equiv.Perm (Vertex n))
    (hσ : ∀ i j : Vertex n,
      Arc (singletonAs n t ht htn) i j ↔ Arc (singletonAs n t' ht' ht'n) (σ i) (σ j))
    (h_map_t : σ ⟨t, ht, by omega⟩ = Vertex.last (by omega : 1 ≤ n))
    (k : ℕ) (hk : k + 1 < t)
    (ih : σ ⟨t - k, by omega, by omega⟩ = ⟨n - k, by omega, by omega⟩) :
    σ ⟨t - (k + 1), by omega, by omega⟩ = ⟨n - (k + 1), by omega, by omega⟩ := by
  set vt_k : Vertex n := ⟨t - k, by omega, by omega⟩ with hvt_k_def
  set vt_k1 : Vertex n := ⟨t - (k + 1), by omega, by omega⟩ with hvt_k1_def
  set vn_k : Vertex n := ⟨n - k, by omega, by omega⟩ with hvn_k_def
  -- Build the spine arc: t - k = (t - (k+1)) + 1, so vt_k = vt_k1.next _
  have hvt_k1_lt : vt_k1.value < n := by change t - (k + 1) < n; omega
  have hsrc_eq : vt_k = vt_k1.next hvt_k1_lt := by
    ext; change t - k = t - (k + 1) + 1; omega
  have hspine : Arc (singletonAs n t ht htn) vt_k vt_k1 := by
    rw [hsrc_eq]; exact Arc.spine vt_k1 hvt_k1_lt
  -- Apply σ
  have h_iso := (hσ vt_k vt_k1).mp hspine
  rw [ih] at h_iso
  rw [arc_iff_spine_or_overlay] at h_iso
  rcases h_iso with ⟨h_lt, h_eq⟩ | ⟨h_R, h_C, h_le⟩
  · -- Spine: vn_k = (σ vt_k1).next h_lt, so (σ vt_k1).value + 1 = n - k
    ext
    change (σ vt_k1).value = n - (k + 1)
    have := congrArg Vertex.value h_eq
    have h_lhs : vn_k.value = n - k := rfl
    have h_rhs : ((σ vt_k1).next h_lt).value = (σ vt_k1).value + 1 := rfl
    rw [h_lhs, h_rhs] at this
    omega
  · -- Overlay: vn_k ∈ activeRows {t'}, σ vt_k1 ∈ activeCols {t'}, vn_k ≤ σ vt_k1
    exfalso
    have hvn_k_v : vn_k.value = n - k := rfl
    rcases (mem_activeRows_singleton n t' ht' ht'n vn_k).mp h_R with h_one | h_succ
    · -- vn_k.value = 1 → n - k = 1; with hk: k + 1 < t ≤ n - 1, contradiction
      rw [hvn_k_v] at h_one; omega
    · -- vn_k.value = t' + 1 → n - k = t' + 1
      rw [hvn_k_v] at h_succ
      rcases (mem_activeCols_singleton n t' ht' ht'n (σ vt_k1)).mp h_C with hjS | hjn
      · -- (σ vt_k1).value = t'; with h_le: vn_k.value ≤ (σ vt_k1).value, contradiction
        have h_le_v : vn_k.value ≤ (σ vt_k1).value := h_le
        rw [hvn_k_v, hjS] at h_le_v; omega
      · -- (σ vt_k1).value = n → σ vt_k1 = Vertex.last; injectivity gives vt_k1 = ⟨t,_,_⟩
        have h_left : σ vt_k1 = Vertex.last (by omega : 1 ≤ n) := by
          ext; rw [hjn]; rfl
        have h_eq_inj := σ.injective (h_left.trans h_map_t.symm)
        have h_val := congrArg Vertex.value h_eq_inj
        have hvt_k1_v : vt_k1.value = t - (k + 1) := rfl
        have ht_v : (⟨t, ht, by omega⟩ : Vertex n).value = t := rfl
        rw [hvt_k1_v, ht_v] at h_val
        omega

/-! ## Mathematical layer — Paper: Lemma 11 (uniqueness direction) -/

/-- **Math.** If `D_n({t}) ≅ D_n({t'})`, then `{t, n - t} = {t', n - t'}` as
finsets. Paper: Lemma 11 (uniqueness direction). -/
theorem singleton_iso_unique (n : ℕ) (t t' : ℕ) (hn : 2 ≤ n)
    (ht : 1 ≤ t) (htn : t ≤ n - 1) (ht' : 1 ≤ t') (ht'n : t' ≤ n - 1)
    (hiso : (singletonAs n t ht htn).digraph ≅ (singletonAs n t' ht' ht'n).digraph) :
    ({t, n - t} : Finset ℕ) = {t', n - t'} := by
  obtain ⟨σRel⟩ := hiso
  set σ : Equiv.Perm (Vertex n) := σRel.toEquiv with hσ_def
  have hσ : ∀ i j : Vertex n,
      Arc (singletonAs n t ht htn) i j ↔ Arc (singletonAs n t' ht' ht'n) (σ i) (σ j) := by
    intro i j
    rw [arc_iff_digraph, arc_iff_digraph]
    exact σRel.map_rel_iff'.symm
  have hn1 : 1 ≤ n := by omega
  set vlast := Vertex.last hn1 with hvlast_def
  set vfirst := Vertex.first hn1 with hvfirst_def
  have h_in_deg := inDeg_eq_two_iff_singleton n t hn ht htn
  have h_in_deg' := inDeg_eq_two_iff_singleton n t' hn ht' ht'n
  have h_map : ∀ v : Vertex n, (v.value = t ∨ v.value = n) ↔
      ((σ v).value = t' ∨ (σ v).value = n) := by
    intro v
    rw [← h_in_deg v, ← h_in_deg' (σ v)]
    exact (iso_preserves_inDeg (singletonAs n t ht htn) (singletonAs n t' ht' ht'n) σ hσ v) ▸
      Iff.rfl
  by_cases h_case : σ vlast = vlast
  · -- σ fixes vlast → S = S' → t = t'
    have h_eq_S := fixes_last_implies_id (singletonAs n t ht htn) (singletonAs n t' ht' ht'n)
      hn σ hσ h_case
    have h_elem : ({⟨t, ht, htn⟩} : Finset (Vertex (n-1))) =
                  ({⟨t', ht', ht'n⟩} : Finset (Vertex (n-1))) := by
      have := congrArg ActiveSet.elements h_eq_S
      simpa [singletonAs] using this
    have h_eq_v : (⟨t, ht, htn⟩ : Vertex (n-1)) = ⟨t', ht', ht'n⟩ :=
      Finset.singleton_inj.mp h_elem
    have h_t_eq : t = t' := congrArg Vertex.value h_eq_v
    rw [h_t_eq]
  · -- σ does not fix vlast → descent gives t' = n - t
    have h_map_t : σ ⟨t, ht, by omega⟩ = vlast :=
      sigma_maps_t_to_n_minus_1 n t t' hn ht htn ht'n σ h_map h_case
    have h_descent : ∀ (k : ℕ) (h_le : k + 1 ≤ t),
        σ (⟨t - k, by omega, by omega⟩ : Vertex n) =
        (⟨n - k, by omega, by omega⟩ : Vertex n) := by
      intro k
      induction k with
      | zero =>
        intro _
        have h_eq : (⟨t - 0, by omega, by omega⟩ : Vertex n) = ⟨t, ht, by omega⟩ := by
          ext; change t - 0 = t; omega
        have h_eq2 : (⟨n - 0, by omega, by omega⟩ : Vertex n) = vlast := by
          ext; change n - 0 = n; omega
        rw [h_eq, h_eq2]; exact h_map_t
      | succ k ih_k =>
        intro hk_le
        exact sigma_descent_step n t t' hn ht htn ht' ht'n σ hσ h_map_t k (by omega)
          (ih_k (by omega))
    have h_map_t' :
        σ vfirst = vlast.subtract (t - 1) (by have : vlast.value = n := rfl; omega) := by
      have h := h_descent (t - 1) (by omega)
      have h_eq1 : (⟨t - (t - 1), by omega, by omega⟩ : Vertex n) = vfirst := by
        ext; change t - (t - 1) = 1; omega
      have h_eq2 : (⟨n - (t - 1), by omega, by omega⟩ : Vertex n) =
                   vlast.subtract (t - 1) (by have : vlast.value = n := rfl; omega) := by
        ext; rfl
      rw [h_eq1, h_eq2] at h
      exact h
    have h_t'_eq : t' = n - t := by
      have h_arc : Arc (singletonAs n t ht htn) vfirst vlast :=
        Arc.overlay _ _ (ActiveSet.first_mem_activeRows _ _)
          (ActiveSet.last_mem_activeCols _ _) (by change 1 ≤ n; omega)
      have h_arc_img := (hσ vfirst vlast).mp h_arc
      rw [h_map_t'] at h_arc_img
      have h_sigma_vlast_v : (σ vlast).value = t' := by
        have := (h_map vlast).mp (Or.inr rfl)
        rcases this with h | h
        · exact h
        · exfalso; apply h_case; ext; rw [h]; rfl
      have hi_v :
          (vlast.subtract (t - 1) (by have : vlast.value = n := rfl; omega)
            : Vertex n).value = n - t + 1 := by
        change n - (t - 1) = n - t + 1; omega
      rw [arc_singleton_iff n t' ht' ht'n] at h_arc_img
      rcases h_arc_img with ⟨_, h_eq⟩ | ⟨h_R, _, _⟩
      · rw [hi_v, h_sigma_vlast_v] at h_eq; omega
      · rcases h_R with h | h
        · rw [hi_v] at h; omega
        · rw [hi_v] at h; omega
    rw [h_t'_eq, show n - (n - t) = t from by omega]
    exact Finset.pair_comm _ _

end HessenbergDigraphs
