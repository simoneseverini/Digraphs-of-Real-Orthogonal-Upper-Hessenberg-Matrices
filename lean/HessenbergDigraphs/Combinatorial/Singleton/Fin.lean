/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Vertex
import HessenbergDigraphs.ActiveSet
import HessenbergDigraphs.Combinatorial.Arc
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Aesop

/-!
# Singleton-set Fin-side engineering

Fin-typed engineering layer for the singleton-set isomorphism
`D_n({t}) ≅ D_n({n - t})`. Houses:

* the basic singleton active-set API (`singletonAs`, the `mem_activeRows`
  / `mem_activeCols` characterizations, the `arc_singleton_iff`
  disjunctive view, and the `Fin n`-aligned `arc_singleton_ofFin_iff`
  bridge);
* the Fin-typed cyclic shift (`cyclicShiftFin`) and its injectivity;
* the modular-arithmetic case analyses (`cyclicShift_arc_forward_fin`,
  `cyclicShift_arc_backward_spine_case`,
  `cyclicShift_arc_backward_fin`) that drive the arc-preservation
  proofs.

The user-facing Vertex-typed `cyclicShift` and the `singleton_iso` /
`singleton_iso_unique` paper theorems live in
`HessenbergDigraphs.Combinatorial.Singleton.Iso`.

## Main definitions

* `singletonAs n t ht htn` — singleton active set `{⟨t, _, _⟩}`.
* `cyclicShiftFin n t hn` — Fin-typed cyclic shift used internally.

## Main results

* `arc_singleton_iff`, `arc_singleton_ofFin_iff` — disjunctive
  characterizations of `Arc (singletonAs ...) i j`.
* `cyclicShift_arc_forward_fin`, `cyclicShift_arc_backward_fin` —
  the Fin-typed forward / backward arc-preservation lemmas.

## References

Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" —
Lemma 11.
-/

namespace HessenbergDigraphs

open Finset Nat

section SingletonSet

/-! ## Mathematical layer — singleton active-set constructor. -/

/-- **Math.** Build the singleton active set `{⟨t, _, _⟩}` as an `ActiveSet n`. -/
def singletonAs (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n - 1) : ActiveSet n :=
  ⟨{⟨t, ht, htn⟩}⟩

@[simp] theorem singletonAs_elements (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n - 1) :
    (singletonAs n t ht htn).elements = {⟨t, ht, htn⟩} := rfl

@[simp] theorem singletonAs_card (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n - 1) :
    (singletonAs n t ht htn).elements.card = 1 := by
  simp [singletonAs]

theorem mem_activeRows_singleton (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n - 1)
    (v : Vertex n) :
    v ∈ (singletonAs n t ht htn).activeRows ↔ v.value = 1 ∨ v.value = t + 1 := by
  rw [ActiveSet.mem_activeRows_iff]
  simp [singletonAs]
  constructor
  · rintro (h | h)
    · left; exact h
    · right; omega
  · rintro (h | h)
    · left; exact h
    · right; omega

theorem mem_activeCols_singleton (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n - 1)
    (v : Vertex n) :
    v ∈ (singletonAs n t ht htn).activeCols ↔ v.value = t ∨ v.value = n := by
  rw [ActiveSet.mem_activeCols_iff]
  simp [singletonAs]
  exact or_congr_left eq_comm

/-- **Math.** Disjunctive characterization of `Arc (singletonAs n t) i j`. -/
theorem arc_singleton_iff (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n - 1)
    (i j : Vertex n) :
    Arc (singletonAs n t ht htn) i j ↔
      (j.value + 1 ≤ n ∧ i.value = j.value + 1) ∨
      ((i.value = 1 ∨ i.value = t + 1) ∧ (j.value = t ∨ j.value = n) ∧
        i.value ≤ j.value) := by
  rw [arc_iff_spine_or_overlay]
  constructor
  · rintro (⟨h_lt, hi_eq⟩ | ⟨hi, hj, hij⟩)
    · left
      refine ⟨h_lt, ?_⟩
      have := congrArg Vertex.value hi_eq
      simpa using this
    · right
      exact ⟨(mem_activeRows_singleton n t ht htn i).mp hi,
             (mem_activeCols_singleton n t ht htn j).mp hj,
             hij⟩
  · rintro (⟨h_lt, hi_eq⟩ | ⟨h_R, h_C, hij⟩)
    · left
      refine ⟨h_lt, ?_⟩
      ext; change i.value = j.value + 1; exact hi_eq
    · right
      exact ⟨(mem_activeRows_singleton n t ht htn i).mpr h_R,
             (mem_activeCols_singleton n t ht htn j).mpr h_C,
             hij⟩

/-- **Mixed.** The same as `arc_singleton_iff`, but with vertices given as
`Vertex.ofFin i`/`Vertex.ofFin j`, in the legacy-aligned simp-normal form
that the modular-arithmetic proofs in this file consume. -/
theorem arc_singleton_ofFin_iff (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n - 1)
    (i j : Fin n) :
    Arc (singletonAs n t ht htn) (Vertex.ofFin i) (Vertex.ofFin j) ↔
      (j.val + 1 + 1 ≤ n ∧ i.val = j.val + 1) ∨
      ((i.val = 0 ∨ i.val = t) ∧ (j.val + 1 = t ∨ j.val + 1 = n) ∧ i.val ≤ j.val) := by
  have hn : 2 ≤ n := by have := i.isLt; omega
  rw [arc_singleton_iff n t ht htn (Vertex.ofFin i) (Vertex.ofFin j)]
  change ((Vertex.ofFin j).value + 1 ≤ n ∧ (Vertex.ofFin i).value = (Vertex.ofFin j).value + 1) ∨
        _ ↔ _
  change (j.val + 1 + 1 ≤ n ∧ i.val + 1 = j.val + 1 + 1) ∨
        ((i.val + 1 = 1 ∨ i.val + 1 = t + 1) ∧
         (j.val + 1 = t ∨ j.val + 1 = n) ∧ i.val + 1 ≤ j.val + 1) ↔ _
  omega

end SingletonSet

section CyclicShiftWitness

/-! ## Mathematical layer — Paper: Lemma 11 witness (`σ_t` cyclic shift) -/

/-! ### Internal Fin-typed helper for the modular-arithmetic proofs. -/

/-- **Eng.** Internal Fin-typed cyclic shift. Hidden behind `cyclicShift` (Vertex-typed)
at the user-facing API; only exists so the modular-arithmetic proofs in this
file (and the Vertex wrappers in `Combinatorial.Singleton.Iso`) have a clean
`Fin n → Fin n` interface to work with. -/
def cyclicShiftFin (n t : ℕ) (hn : 2 ≤ n) : Fin n → Fin n :=
  fun i => ⟨(i.val + n - t) % n, Nat.mod_lt _ (by omega)⟩

/-- **Mixed.** The Fin-typed cyclic shift is injective. -/
theorem cyclicShiftFin_injective (n t : ℕ) (hn : 2 ≤ n)
    (_ht : 1 ≤ t) (htn : t ≤ n - 1) :
    Function.Injective (cyclicShiftFin n t hn) := by
  intro i j hij
  simp_all +decide [cyclicShiftFin, Fin.ext_iff]
  have := Nat.modEq_iff_dvd.mp hij.symm
  obtain ⟨k, hk⟩ := this
  rw [Nat.cast_sub (by linarith [Fin.is_lt i, Nat.sub_add_cancel (by linarith : 1 ≤ n)]),
      Nat.cast_sub (by linarith [Fin.is_lt j, Nat.sub_add_cancel (by linarith : 1 ≤ n)])] at hk
  norm_num at hk
  exact_mod_cast (by
    nlinarith [show k = 0 by
      nlinarith [Fin.is_lt i, Fin.is_lt j, Nat.sub_add_cancel (by linarith : 1 ≤ n)]]
    : (i : ℤ) = j)

/-! ## Engineering layer — Type B (modular arithmetic case analysis):
    forward direction; each branch peels `% n` via `rcases n with (_|_|n)` and
    `simp_all +arith +decide` chains over the boundary cases. -/

/-- **Mixed.** Forward direction of the singleton-isomorphism arc preservation
(Fin-typed internal form, consumed by the Vertex-typed wrapper in
`Combinatorial.Singleton.Iso`). -/
lemma cyclicShift_arc_forward_fin
    (n t : ℕ) (hn : 2 ≤ n) (ht : 1 ≤ t) (htn : t ≤ n - 1) (i j : Fin n)
    (h : Arc (singletonAs n t ht htn) (Vertex.ofFin i) (Vertex.ofFin j)) :
    Arc (singletonAs n (n - t) (by omega) (by omega))
        (Vertex.ofFin (cyclicShiftFin n t hn i))
        (Vertex.ofFin (cyclicShiftFin n t hn j)) := by
  rw [arc_singleton_ofFin_iff] at h
  rw [arc_singleton_ofFin_iff]
  unfold cyclicShiftFin at *
  rcases h with (⟨hj₁, hj₂⟩ | ⟨hj₁ | hj₁, hj₂ | hj₂, hj₃⟩) <;> simp_all +decide
  · rw [show (j + 1 + n - t : ℕ) = (j + n - t) + 1 by omega]
    by_cases h : (j + n - t : ℕ) % n = n - 1
    · rcases n with (_ | _ | n) <;> simp_all +decide
      norm_num [Nat.add_mod, h]
    · refine Or.inl ⟨?_, ?_⟩
      · exact Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.mod_lt _ (by linarith))) (by omega)
      · rw [Nat.add_mod, Nat.mod_eq_of_lt]
        · rcases n with (_ | _ | n) <;> aesop
        · rcases n with (_ | _ | n) <;> simp_all +arith +decide [Nat.mod_eq_of_lt]
          exact Nat.le_of_lt_succ (lt_of_le_of_ne
            (Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))) h)
  · rcases n with (_ | _ | n) <;> simp_all +arith +decide [Nat.mod_eq_of_lt]
    omega
  · rcases n with (_ | _ | n) <;> simp_all +arith +decide [Nat.mod_eq_of_lt]
    rw [show 2 * n + 3 - t = (n + 2) + (n + 1 - t) by omega, Nat.add_mod]
    norm_num [Nat.mod_eq_of_lt (by omega : n + 1 - t < n + 2)]
    exact Or.inl ⟨ht, by omega⟩
  · omega
  · rcases n with (_ | _ | n) <;> simp_all +arith +decide
    rw [show 2 * n + 3 - t = (n + 2) + (n + 1 - t) by omega, Nat.add_mod]
    norm_num [Nat.mod_eq_of_lt (by omega : n + 1 - t < n + 2)]
    exact Or.inl (by omega)

/-! ## Engineering layer — Type B/C (Int.ModEq + lt_trichotomy on ℤ winding):
    spine sub-case of the backward direction. -/

/-- **Eng.** Spine sub-case of `cyclicShift_arc_backward`: when the cyclically-
shifted indices satisfy a spine relation in `D_n({n - t})`, the original
indices satisfy either a spine relation (no wrap-around) or the
overlay relation `1 → n` (wrap-around). -/
private lemma cyclicShift_arc_backward_spine_case
    (n t : ℕ) (hn : 2 ≤ n) (htn : t ≤ n - 1) (i j : Fin n)
    (h₁ : (j.val + n - t) % n + 1 + 1 ≤ n)
    (h₂ : (i.val + n - t) % n = (j.val + n - t) % n + 1) :
    (j.val + 1 + 1 ≤ n ∧ i.val = j.val + 1) ∨
    ((i.val = 0 ∨ i.val = t) ∧ (j.val + 1 = t ∨ j.val + 1 = n) ∧ i.val ≤ j.val) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (i + n - t : ℤ) = (j + n - t : ℤ) + 1 + k * n := by
    have h_eq : (i + n - t : ℤ) ≡ (j + n - t : ℤ) + 1 [ZMOD n] := by
      norm_cast
      rw [Int.subNatNat_of_le, Int.subNatNat_of_le] <;> norm_cast
      · simp +decide [Nat.ModEq, Nat.add_mod, h₂]
        norm_num [Nat.mod_eq_of_lt h₁]
      · omega
      · omega
    exact h_eq.symm.dvd.imp fun k hk => by linarith
  rcases lt_trichotomy k 0 with hk' | rfl | hk' <;>
    try nlinarith [Fin.is_lt i, Fin.is_lt j]
  · exact Or.inr ⟨Or.inl <| by nlinarith [Fin.is_lt i, Fin.is_lt j],
      Or.inr <| by nlinarith [Fin.is_lt i, Fin.is_lt j],
      Nat.le_of_lt_succ <| by nlinarith [Fin.is_lt i, Fin.is_lt j]⟩
  · exact Or.inl ⟨by linarith [Fin.is_lt i, Fin.is_lt j],
      by linarith [Fin.is_lt i, Fin.is_lt j]⟩

/-! ## Engineering layer — Type B/C (4-way overlay case analysis):
    backward direction; `rcases h₂ × rcases h₁` × `rcases n × rcases k` over
    mod-arithmetic; spine sub-case extracted to
    `cyclicShift_arc_backward_spine_case`. -/

/-- **Mixed.** Backward direction of the singleton-isomorphism arc preservation
(Fin-typed internal form, consumed by the Vertex-typed wrapper in
`Combinatorial.Singleton.Iso`). -/
lemma cyclicShift_arc_backward_fin
    (n t : ℕ) (hn : 2 ≤ n) (ht : 1 ≤ t) (htn : t ≤ n - 1) (i j : Fin n)
    (h : Arc (singletonAs n (n - t) (by omega) (by omega))
        (Vertex.ofFin (cyclicShiftFin n t hn i))
        (Vertex.ofFin (cyclicShiftFin n t hn j))) :
    Arc (singletonAs n t ht htn) (Vertex.ofFin i) (Vertex.ofFin j) := by
  rw [arc_singleton_ofFin_iff] at h
  rw [arc_singleton_ofFin_iff]
  unfold cyclicShiftFin at *
  rcases h with (⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩)
  · exact cyclicShift_arc_backward_spine_case n t hn htn i j h₁ (by omega)
  · rcases h₂ with (h₂ | h₂) <;> rcases h₁ with (h₁ | h₁) <;> simp_all +decide
    · rw [← Nat.dvd_iff_mod_eq_zero] at h₁
      obtain ⟨k, hk⟩ := h₁
      rcases k with (_ | _ | k) <;> simp_all +decide [Nat.mul_succ]
      · omega
      · rcases n with (_ | _ | n) <;> simp_all +arith +decide
        rw [show (n + j + 2 - t) = (n + 2 - t) + j by omega] at h₂
        simp_all +arith +decide
        by_cases h : (j : ℕ) + (n + 2 - t) < n + 2 <;> simp_all +decide [Nat.mod_eq_of_lt]
        · grind
        · rw [Nat.mod_eq_sub_mod] at h₂ <;> try omega
          rw [Nat.mod_eq_of_lt] at h₂ <;> omega
      · grind
    · omega
    · rw [← Nat.dvd_iff_mod_eq_zero] at h₁
      obtain ⟨k, hk⟩ := h₁
      rcases k with (_ | _ | k) <;> simp_all +decide [Nat.mul_succ]
      · omega
      · rcases n with (_ | _ | n) <;> simp_all +arith +decide
        have := Nat.mod_add_div (n + j + 2 - t) (n + 2)
        simp_all +decide
        rcases k : (n + j + 2 - t) / (n + 2) with (_ | _ | k) <;>
          simp_all +arith +decide [Nat.mod_eq_of_lt]
        · exact Or.inl ⟨by omega, by omega⟩
        · omega
        · nlinarith [Nat.sub_le (n + j + 2) t, Fin.is_lt j]
      · grind
    · rcases n with (_ | _ | n) <;> first | omega | simp_all +arith +decide
      have := Nat.mod_add_div (n + j + 2 - t) (n + 2)
      have := Nat.mod_add_div (n + i + 2 - t) (n + 2)
      simp_all +arith +decide
      rcases k : (n + j + 2 - t) / (n + 2) with (_ | _ | k) <;>
        simp_all +arith +decide [Nat.mod_eq_of_lt]
      · rcases k : (n + i + 2 - t) / (n + 2) with (_ | _ | k) <;>
          simp_all +arith +decide [Nat.mod_eq_of_lt]
        · grind
        · omega
        · nlinarith [Nat.sub_add_cancel (show t ≤ n + 2 from by omega),
            Nat.sub_add_cancel (show t ≤ n + ↑i + 2 from by omega),
            Fin.is_lt i, Fin.is_lt j]
      · omega
      · nlinarith [Nat.sub_le (n + j + 2) t, Fin.is_lt j]

end CyclicShiftWitness

end HessenbergDigraphs
