/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Vertex
import HessenbergDigraphs.ActiveSet
import HessenbergDigraphs.Combinatorial.Digraph
import HessenbergDigraphs.Combinatorial.Cut
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card

/-!
# Automorphism rigidity for `D_n(S)` with `|S| ≥ 2` (bundled-structure form)
-/

namespace HessenbergDigraphs

open Finset Nat Digraph

variable {n : ℕ} (S S' : ActiveSet n)

/-- **Math.** The canonical wrap-around overlay arc `first → last`. -/
private lemma arc_first_to_last (hn : 2 ≤ n) :
    Arc S (Vertex.first (by omega : 1 ≤ n)) (Vertex.last (by omega : 1 ≤ n)) :=
  Arc.overlay _ _
    (ActiveSet.first_mem_activeRows _ _)
    (ActiveSet.last_mem_activeCols _ _)
    (by change (Vertex.first (by omega : 1 ≤ n)).value ≤ (Vertex.last (by omega : 1 ≤ n)).value
        change 1 ≤ n; omega)

/-- **Mixed.** One descent step: if `σ` already fixes `Vertex.last` and every `j` with
`j.value > k.value`, then `σ k = k`. -/
private lemma sigma_fixes_step_via_spine (hn : 2 ≤ n)
    (σ : Equiv.Perm (Vertex n))
    (hσ : ∀ i j : Vertex n, Arc S i j ↔ Arc S' (σ i) (σ j))
    (hfix : σ (Vertex.last (by omega : 1 ≤ n)) = Vertex.last (by omega : 1 ≤ n))
    (k : Vertex n)
    (hk_ind : ∀ j : Vertex n, j.value > k.value → σ j = j) :
    σ k = k := by
  by_cases hk : k.value = n
  · have hk_eq : k = Vertex.last (by omega : 1 ≤ n) := by ext; exact hk
    rw [hk_eq]; exact hfix
  · have hk_lt : k.value < n := by have := k.value_le_n; omega
    -- Build spine arc k.next hk_lt → k
    have h_arc_S : Arc S (k.next hk_lt) k := Arc.spine k hk_lt
    have h_arc_S' : Arc S' (σ (k.next hk_lt)) (σ k) := (hσ _ _).mp h_arc_S
    have h_fix_succ : σ (k.next hk_lt) = k.next hk_lt :=
      hk_ind (k.next hk_lt) (by change k.value + 1 > k.value; omega)
    rw [h_fix_succ] at h_arc_S'
    have h_sigma_k_le_k : (σ k).value ≤ k.value := by
      by_contra hgt
      push_neg at hgt
      have hk' := hk_ind (σ k) hgt
      have := σ.injective hk'
      have h_value : (σ k).value = k.value := by rw [this]
      omega
    obtain ⟨h_lt, hi_eq⟩ := backward_arc_is_spine S' (k.next hk_lt) (σ k) h_arc_S' (by
      show (σ k).value < (k.next hk_lt).value
      change (σ k).value < k.value + 1
      omega)
    have h_value : (σ k).value = k.value := by
      have h_succ_v : (k.next hk_lt).value = k.value + 1 := rfl
      have h_next_v : ((σ k).next h_lt).value = (σ k).value + 1 := rfl
      have := congrArg Vertex.value hi_eq
      rw [h_succ_v, h_next_v] at this
      omega
    ext; exact h_value

/-- **Math.** If a digraph isomorphism fixes `Vertex.last`, it forces `S = S'`. -/
theorem fixes_last_implies_id (hn : 2 ≤ n)
    (σ : Equiv.Perm (Vertex n))
    (hσ : ∀ i j : Vertex n, Arc S i j ↔ Arc S' (σ i) (σ j))
    (hfix : σ (Vertex.last (by omega : 1 ≤ n)) = Vertex.last (by omega : 1 ≤ n)) :
    S = S' := by
  -- σ is the identity
  have h_ind : ∀ k : Vertex n, σ k = k := by
    have h_step := sigma_fixes_step_via_spine S S' hn σ hσ hfix
    intro k
    -- Strong induction over k.value (descending)
    by_contra hne
    -- Take the maximum k where σ k ≠ k
    have h_set_ne : (Finset.univ.filter (fun k : Vertex n => σ k ≠ k)).Nonempty :=
      ⟨k, by simp [hne]⟩
    obtain ⟨km, hm_mem, hm_max⟩ :=
      Finset.exists_max_image _ (fun v : Vertex n => v.value) h_set_ne
    rw [Finset.mem_filter] at hm_mem
    apply hm_mem.2
    apply h_step
    intro j hjv
    by_contra hj_ne
    have : km.value ≥ j.value := by
      apply hm_max
      simp [hj_ne]
    omega
  -- Now show S = S' using the fact that σ is the identity
  ext k
  -- Build the corresponding Vertex n with value k.value
  let v : Vertex n :=
    ⟨k.value, k.one_le_value, by have := k.value_le_n; omega⟩
  have hv_lt : v.value < n := by
    change k.value < n
    have := k.value_le_n
    omega
  have h_S_iff_ex : k ∈ S.elements ↔ ∃ y ∈ S.elements, y.value = v.value := by
    constructor
    · intro hk; exact ⟨k, hk, rfl⟩
    · rintro ⟨y, hyS, hyv⟩
      have hy_eq : y = k := by ext; exact hyv
      rw [← hy_eq]; exact hyS
  have h_S'_iff_ex : k ∈ S'.elements ↔ ∃ y ∈ S'.elements, y.value = v.value := by
    constructor
    · intro hk; exact ⟨k, hk, rfl⟩
    · rintro ⟨y, hyS, hyv⟩
      have hy_eq : y = k := by ext; exact hyv
      rw [← hy_eq]; exact hyS
  have h_arc_eq : Arc S (Vertex.first (by omega : 1 ≤ n)) v ↔
                  Arc S' (Vertex.first (by omega : 1 ≤ n)) v := by
    have h := hσ (Vertex.first (by omega : 1 ≤ n)) v
    rw [h_ind, h_ind] at h
    exact h
  rw [h_S_iff_ex, h_S'_iff_ex,
      mem_S_iff_arc_from_first S v hn hv_lt,
      h_arc_eq,
      ← mem_S_iff_arc_from_first S' v hn hv_lt]

/-! ## Mathematical layer — interior non-active-col vertex has in-degree 1. -/

/-- **Math.** For an interior `v` (with `v.value < n`) not in `S.activeCols`, the
in-degree of `v` is exactly 1. -/
theorem inDeg_eq_one_of_not_mem_activeCols (v : Vertex n)
    (hvn : v.value < n) (hnoC : v ∉ S.activeCols) :
    inDeg S v = 1 := by
  unfold inDeg
  have h_filter : (Finset.univ : Finset (Vertex n)).filter (fun i => Arc S i v) =
                  {v.next hvn} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro harc
      rcases (arc_iff_spine_or_overlay S i v).mp harc with ⟨_, hi_eq⟩ | ⟨_, hjC, _⟩
      · ext
        have := congrArg Vertex.value hi_eq
        change i.value = (v.next hvn).value
        change i.value = v.value + 1
        have h_v : (v.next hvn).value = v.value + 1 := rfl
        rw [h_v] at this
        exact this
      · exact absurd hjC hnoC
    · intro hi
      rw [hi]
      exact Arc.spine v hvn
  rw [h_filter, Finset.card_singleton]

/-! ## Engineering layer — pigeonhole below the cut. -/

private theorem perm_image_below_cut (hn : 2 ≤ n)
    (σ : Equiv.Perm (Vertex n))
    (hσ : ∀ i j : Vertex n, Arc S i j ↔ Arc S' (σ i) (σ j))
    (w : Vertex n) (hw_def : w = σ (Vertex.last (by omega : 1 ≤ n)))
    (hwlt : w.value < n)
    (hσf_lt : (σ (Vertex.first (by omega : 1 ≤ n))).value < w.value) : False := by
  have hn1 : 1 ≤ n := by omega
  have hall : ∀ m : ℕ, m + 1 ≤ n - 1 →
      ∀ (h_le : m + 1 ≤ n) (h_pos : 1 ≤ m + 1),
      (σ (⟨m + 1, h_pos, h_le⟩ : Vertex n)).value < w.value := by
    intro m
    induction m with
    | zero =>
      intro _ h_le h_pos
      have h_eq : (⟨1, h_pos, h_le⟩ : Vertex n) = Vertex.first hn1 := by ext; rfl
      rw [h_eq]; exact hσf_lt
    | succ k ih =>
      intro hk h_le h_pos
      by_contra hge
      push_neg at hge
      have hk_le_n : k + 1 ≤ n := by omega
      have hk_pos : 1 ≤ k + 1 := by omega
      have hsi_ne_w : σ ⟨k + 1 + 1, h_pos, h_le⟩ ≠ w := by
        intro heq
        rw [hw_def] at heq
        have h_eq := σ.injective heq
        have hkn : k + 1 + 1 = n := by
          have := congrArg Vertex.value h_eq
          exact this
        omega
      have hsi_ne_w_val : (σ ⟨k + 1 + 1, h_pos, h_le⟩).value ≠ w.value := by
        intro heq; apply hsi_ne_w; ext; exact heq
      have ih_val := ih (by omega) hk_le_n hk_pos
      have hk1_lt : (⟨k + 1, hk_pos, hk_le_n⟩ : Vertex n).value < n := by
        change k + 1 < n; omega
      have hspine_eq :
          (⟨k + 1, hk_pos, hk_le_n⟩ : Vertex n).next hk1_lt =
          ⟨k + 1 + 1, h_pos, h_le⟩ := by ext; rfl
      have hspine : Arc S (⟨k + 1 + 1, h_pos, h_le⟩ : Vertex n)
                          (⟨k + 1, hk_pos, hk_le_n⟩ : Vertex n) := by
        rw [← hspine_eq]; exact Arc.spine _ hk1_lt
      have harc_img := (hσ _ _).mp hspine
      have hcut := cut_lemma S' (w.value - 1)
        (σ ⟨k + 1 + 1, h_pos, h_le⟩) (σ ⟨k + 1, hk_pos, hk_le_n⟩)
        harc_img (by have := w.one_le_value; omega) (by omega)
      have h_eq : (σ ⟨k + 1 + 1, h_pos, h_le⟩).value = w.value := by
        have := hcut.1; have := w.one_le_value; omega
      exact hsi_ne_w_val h_eq
  -- Cardinality contradiction
  suffices h_card : n - 1 ≤ w.value - 1 by have := w.one_le_value; omega
  have hinj : Function.Injective
      (fun i : Fin (n - 1) =>
        (⟨(σ (Vertex.ofFinSucc i)).value - 1,
          by have := hall i.val (by omega) (by omega) (by omega)
             have h_def : (σ (Vertex.ofFinSucc i)).value =
                 (σ (⟨i.val + 1, by omega, by omega⟩ : Vertex n)).value := rfl
             have := (σ (Vertex.ofFinSucc i)).one_le_value
             omega⟩ : Fin (w.value - 1))) := by
    intro a b hab
    have hab' : (σ (Vertex.ofFinSucc a)).value - 1 =
                (σ (Vertex.ofFinSucc b)).value - 1 :=
      Fin.mk_eq_mk.mp hab
    have h_va_pos := (σ (Vertex.ofFinSucc a)).one_le_value
    have h_vb_pos := (σ (Vertex.ofFinSucc b)).one_le_value
    have hval_eq : (σ (Vertex.ofFinSucc a)).value =
                   (σ (Vertex.ofFinSucc b)).value := by omega
    have h_eq : σ (Vertex.ofFinSucc a) =
                σ (Vertex.ofFinSucc b) :=
      Vertex.ext hval_eq
    have h_inj := σ.injective h_eq
    have h_v : a.val + 1 = b.val + 1 := congrArg Vertex.value h_inj
    apply Fin.ext
    show a.val = b.val
    omega
  have h_le := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at h_le
  omega

/-! ## Engineering layer — pigeonhole above the cut. -/

private theorem perm_image_above_cut (hn : 2 ≤ n)
    (hcard : 2 ≤ S.elements.card)
    (σ : Equiv.Perm (Vertex n))
    (hσ : ∀ i j : Vertex n, Arc S i j ↔ Arc S' (σ i) (σ j))
    (w : Vertex n) (hw_def : w = σ (Vertex.last (by omega : 1 ≤ n)))
    (_hwlt : w.value < n)
    (hno_above : ∀ s ∈ S'.elements, s.value ≤ w.value)
    (hσ0_ge : (σ (Vertex.first (by omega : 1 ≤ n))).value ≥ w.value)
    (hσ0_ne_w : σ (Vertex.first (by omega : 1 ≤ n)) ≠ w) : False := by
  set vfirst := Vertex.first (by omega : 1 ≤ n) with hvf_def
  set vlast := Vertex.last (by omega : 1 ≤ n) with hvl_def
  have hσ0_gt : (σ vfirst).value ≥ w.value + 1 := by
    have h_ne : (σ vfirst).value ≠ w.value := fun h => hσ0_ne_w (Vertex.ext h)
    omega
  have harc_1_n : Arc S vfirst vlast := arc_first_to_last S hn
  have hσ_arc : Arc S' (σ vfirst) (σ vlast) := (hσ vfirst vlast).mp harc_1_n
  rw [← hw_def] at hσ_arc
  obtain ⟨h_lt, hi_eq⟩ := backward_arc_is_spine S' (σ vfirst) w hσ_arc (by omega)
  have hσ0_val : (σ vfirst).value = w.value + 1 := by
    have hv := congrArg Vertex.value hi_eq
    have h_next : (w.next h_lt).value = w.value + 1 := rfl
    rw [h_next] at hv
    exact hv
  have harc_target : ∀ j : Vertex n, Arc S' (σ vfirst) j → j = w ∨ j = vlast := by
    intro j harc
    rcases (arc_iff_spine_or_overlay S' (σ vfirst) j).mp harc
      with ⟨h_jlt, hi_eq'⟩ | ⟨_, hjC, hij⟩
    · left
      have hv := congrArg Vertex.value hi_eq'
      have h_next : (j.next h_jlt).value = j.value + 1 := rfl
      rw [h_next] at hv
      ext; show j.value = w.value; omega
    · rcases (ActiveSet.mem_activeCols_iff S' j).mp hjC with ⟨k, hkS, hkv⟩ | hjeq
      · exfalso
        have h1 : (σ vfirst).value ≤ j.value := hij
        have h2 := hno_above k hkS
        omega
      · right; ext; change j.value = vlast.value; change j.value = n; exact hjeq
  obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < S.elements.card)
  set s₁_v : Vertex n := Vertex.castGE (Nat.sub_le n 1) s₁ with hs₁v_def
  set s₂_v : Vertex n := Vertex.castGE (Nat.sub_le n 1) s₂ with hs₂v_def
  have ha₁ : Arc S vfirst s₁_v :=
    Arc.overlay _ _
      (ActiveSet.first_mem_activeRows _ _)
      ((ActiveSet.mem_activeCols_iff S s₁_v).mpr (Or.inl ⟨s₁, hs₁, rfl⟩))
      (by change vfirst.value ≤ s₁_v.value; change 1 ≤ s₁.value; exact s₁.one_le_value)
  have ha₂ : Arc S vfirst s₂_v :=
    Arc.overlay _ _
      (ActiveSet.first_mem_activeRows _ _)
      ((ActiveSet.mem_activeCols_iff S s₂_v).mpr (Or.inl ⟨s₂, hs₂, rfl⟩))
      (by change vfirst.value ≤ s₂_v.value; change 1 ≤ s₂.value; exact s₂.one_le_value)
  have hm₁ : Arc S' (σ vfirst) (σ s₁_v) := (hσ vfirst s₁_v).mp ha₁
  have hm₂ : Arc S' (σ vfirst) (σ s₂_v) := (hσ vfirst s₂_v).mp ha₂
  have hne_img : σ s₁_v ≠ σ s₂_v := by
    intro heq
    apply hne
    have h := σ.injective heq
    have hv := congrArg Vertex.value h
    ext; exact hv
  have hne₁_w : σ s₁_v ≠ w := by
    intro heq
    rw [hw_def] at heq
    have h := σ.injective heq
    have hv := congrArg Vertex.value h
    have h1 : s₁_v.value = s₁.value := rfl
    have h2 : vlast.value = n := rfl
    have hs₁_le : s₁.value ≤ n - 1 := s₁.value_le_n
    rw [h1, h2] at hv
    omega
  have hne₂_w : σ s₂_v ≠ w := by
    intro heq
    rw [hw_def] at heq
    have h := σ.injective heq
    have hv := congrArg Vertex.value h
    have h1 : s₂_v.value = s₂.value := rfl
    have h2 : vlast.value = n := rfl
    have hs₂_le : s₂.value ≤ n - 1 := s₂.value_le_n
    rw [h1, h2] at hv
    omega
  have h_eq₁ : σ s₁_v = vlast := by
    rcases harc_target _ hm₁ with h | h
    · exact absurd h hne₁_w
    · exact h
  have h_eq₂ : σ s₂_v = vlast := by
    rcases harc_target _ hm₂ with h | h
    · exact absurd h hne₂_w
    · exact h
  exact hne_img (h_eq₁.trans h_eq₂.symm)

/-! ## Mathematical layer — Paper Theorem 10 (Rigidity). -/

/-- **Math.** Rigidity: if `|S|, |S'| ≥ 2`, then `S.digraph ≅ S'.digraph` forces
`S = S'`. -/
theorem rigid (hn : 2 ≤ n)
    (hcard : 2 ≤ S.elements.card) (hcard' : 2 ≤ S'.elements.card)
    (hiso : S.digraph ≅ S'.digraph) : S = S' := by
  obtain ⟨σRel⟩ := hiso
  set σ : Equiv.Perm (Vertex n) := σRel.toEquiv with hσ_def
  have hσ : ∀ i j : Vertex n, Arc S i j ↔ Arc S' (σ i) (σ j) := by
    intro i j
    rw [arc_iff_digraph, arc_iff_digraph]
    exact σRel.map_rel_iff'.symm
  have hn1 : 1 ≤ n := by omega
  set vlast : Vertex n := Vertex.last hn1 with hvlast_def
  set vfirst : Vertex n := Vertex.first hn1 with hvfirst_def
  -- Inverse direction
  have hσ_inv : ∀ i j : Vertex n, Arc S' i j ↔ Arc S (σ.symm i) (σ.symm j) := by
    intro i j
    have h := hσ (σ.symm i) (σ.symm j)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h.symm
  have h_fix : σ vlast = vlast := by
    by_contra hne_fix
    set w := σ vlast with hw_def
    have hw_ne : w ≠ vlast := hne_fix
    have hw_lt : w.value < n := by
      have := w.value_le_n
      have hvlast_v : vlast.value = n := rfl
      by_contra h
      push_neg at h
      apply hne_fix
      ext
      have : w.value = n := by omega
      rw [this, hvlast_v]
    -- in-degree of w in D_n(S') equals |S| + 1
    have hinDeg_w : inDeg S' w = S.elements.card + 1 := by
      have h_pres := iso_preserves_inDeg S S' σ hσ vlast
      rw [show σ vlast = w from rfl, inDeg_last S hn] at h_pres
      exact h_pres.symm
    -- w is in S' as an active-column-element
    have hwS' : ∃ k ∈ S'.elements, k.value = w.value := by
      by_contra hno
      push_neg at hno
      have hnoC : w ∉ S'.activeCols := by
        rw [ActiveSet.mem_activeCols_iff]
        push_neg
        refine ⟨hno, ?_⟩
        intro h_eq_n
        apply hne_fix
        ext
        rw [h_eq_n]
        rfl
      have h_one := inDeg_eq_one_of_not_mem_activeCols S' w hw_lt hnoC
      omega
    -- in-degree formula gives |S'.filter (· < w)| = |S| - 1
    obtain ⟨k_w, hk_wS', hk_wv⟩ := hwS'
    have hinDeg_formula := inDeg_mem_S S' w hn ⟨k_w, hk_wS', hk_wv⟩
    have hfilter_eq :
        (S'.elements.filter (fun k => k.value < w.value)).card = S.elements.card - 1 := by
      omega
    -- symmetric direction with σ.symm
    set u := σ.symm vlast with hu_def
    have hu_ne : u ≠ vlast := by
      intro heq
      apply hne_fix
      have : σ vlast = σ u := by rw [heq]
      rw [hu_def, σ.apply_symm_apply] at this
      exact this
    have hu_lt : u.value < n := by
      have := u.value_le_n
      have hvlast_v : vlast.value = n := rfl
      by_contra h
      push_neg at h
      apply hu_ne
      ext
      have : u.value = n := by omega
      rw [this, hvlast_v]
    have hinDeg_u : inDeg S u = S'.elements.card + 1 := by
      have h_pres := iso_preserves_inDeg S' S σ.symm hσ_inv vlast
      rw [show σ.symm vlast = u from rfl, inDeg_last S' hn] at h_pres
      exact h_pres.symm
    have huS : ∃ k ∈ S.elements, k.value = u.value := by
      by_contra hno
      push_neg at hno
      have hnoC : u ∉ S.activeCols := by
        rw [ActiveSet.mem_activeCols_iff]
        push_neg
        refine ⟨hno, ?_⟩
        intro h_eq_n
        apply hu_ne
        ext
        rw [h_eq_n]
        rfl
      have h_one := inDeg_eq_one_of_not_mem_activeCols S u hu_lt hnoC
      omega
    obtain ⟨k_u, hk_uS, hk_uv⟩ := huS
    have hinDeg_u_formula := inDeg_mem_S S u hn ⟨k_u, hk_uS, hk_uv⟩
    have hfilter_u :
        (S.elements.filter (fun k => k.value < u.value)).card = S'.elements.card - 1 := by
      omega
    -- equal cardinalities
    have hcard_eq : S.elements.card = S'.elements.card := by
      have h1 : S.elements.card ≤ S'.elements.card := by
        have h_sub : insert k_w (S'.elements.filter (fun k => k.value < w.value)) ⊆
            S'.elements := by
          rw [Finset.insert_subset_iff]
          exact ⟨hk_wS', Finset.filter_subset _ _⟩
        have h_notmem : k_w ∉ S'.elements.filter (fun k => k.value < w.value) := by
          rw [Finset.mem_filter]; intro ⟨_, h⟩; rw [hk_wv] at h; omega
        have h_card_ins := Finset.card_le_card h_sub
        rw [Finset.card_insert_of_notMem h_notmem, hfilter_eq] at h_card_ins
        omega
      have h2 : S'.elements.card ≤ S.elements.card := by
        have h_sub : insert k_u (S.elements.filter (fun k => k.value < u.value)) ⊆
            S.elements := by
          rw [Finset.insert_subset_iff]
          exact ⟨hk_uS, Finset.filter_subset _ _⟩
        have h_notmem : k_u ∉ S.elements.filter (fun k => k.value < u.value) := by
          rw [Finset.mem_filter]; intro ⟨_, h⟩; rw [hk_uv] at h; omega
        have h_card_ins := Finset.card_le_card h_sub
        rw [Finset.card_insert_of_notMem h_notmem, hfilter_u] at h_card_ins
        omega
      omega
    -- no element of S' has value > w.value
    have hno_above : ∀ s ∈ S'.elements, s.value ≤ w.value := by
      intro s hs
      by_contra hgt; push_neg at hgt
      -- The filter below w plus k_w plus s would be ≥ S.card + 1 = S'.card + 1, contradiction
      have hs_ne_kw : s ≠ k_w := by
        intro heq; rw [heq, hk_wv] at hgt; omega
      have h_sub : insert s (insert k_w (S'.elements.filter (fun k => k.value < w.value)))
          ⊆ S'.elements := by
        rw [Finset.insert_subset_iff]
        refine ⟨hs, ?_⟩
        rw [Finset.insert_subset_iff]
        exact ⟨hk_wS', Finset.filter_subset _ _⟩
      have h_notmem_inner : k_w ∉ S'.elements.filter (fun k => k.value < w.value) := by
        rw [Finset.mem_filter]; intro ⟨_, h⟩; rw [hk_wv] at h; omega
      have h_notmem_outer : s ∉ insert k_w (S'.elements.filter (fun k => k.value < w.value)) := by
        rw [Finset.mem_insert, Finset.mem_filter]
        rintro (h | ⟨_, h⟩)
        · exact hs_ne_kw h
        · omega
      have h_card := Finset.card_le_card h_sub
      rw [Finset.card_insert_of_notMem h_notmem_outer,
          Finset.card_insert_of_notMem h_notmem_inner, hfilter_eq] at h_card
      omega
    -- Case split on σ vfirst vs w
    by_cases hσf_eq_w : σ vfirst = w
    · -- σ vfirst = w = σ vlast → vfirst = vlast → n = 1, contradicts hn
      have h_eq : vfirst = vlast := σ.injective (hσf_eq_w.trans hw_def)
      have hv := congrArg Vertex.value h_eq
      have h_f : vfirst.value = 1 := rfl
      have h_l : vlast.value = n := rfl
      rw [h_f, h_l] at hv
      omega
    · by_cases hσf_lt_w : (σ vfirst).value < w.value
      · exact perm_image_below_cut S S' hn σ hσ w hw_def hw_lt hσf_lt_w
      · push_neg at hσf_lt_w
        exact perm_image_above_cut S S' hn hcard σ hσ w hw_def hw_lt hno_above
          hσf_lt_w hσf_eq_w
  exact fixes_last_implies_id S S' hn σ hσ h_fix

end HessenbergDigraphs
