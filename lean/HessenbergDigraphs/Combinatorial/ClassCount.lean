/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import HessenbergDigraphs.Combinatorial.Rigidity
import HessenbergDigraphs.Combinatorial.Singleton.Iso
import HessenbergDigraphs.Combinatorial.Degree
import HessenbergDigraphs.Combinatorial.Enumeration
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Card

/-!
# Counting isomorphism classes of `D_n(S)`

The number of non-isomorphic support digraphs `D_n(S)` for `S ⊆ [n-1]` is
`2^(n-1) - ⌊(n-1)/2⌋` (Paper: Theorem 12). This file upgrades the arithmetic
identity `count_formula` to a genuine cardinality statement: a complete
isomorphism invariant `isoInvariant` whose image has exactly that many
elements.

The invariant separates the three strata that the count decomposes into:

* `|S| ≥ 2`: rigid, so each `S` is its own class (`Sum.inr S`);
* `|S| = 1`: singletons pair up `{t} ≅ {n - t}`, so the class is determined by
  `min t (n - t)` (`Sum.inl`);
* `|S| = 0`: the empty set, a single class (`Sum.inr ∅`).

`isoInvariant_eq_iff` proves it is a complete invariant
(`isoInvariant S = isoInvariant S' ↔ D_n(S) ≅ D_n(S')`), using `rigid`,
`iso_card_eq`, `singleton_iso`, and `singleton_iso_unique`.

## Main results

* `isoInvariant_eq_iff` — completeness of the invariant.
* `card_isoClasses` — `(univ.image isoInvariant).card = 2^(n-1) - (n-1)/2`.
* `card_isoClasses_quot` — the readable form:
  `Nat.card (Quotient (isoSetoid n)) = 2^(n-1) - (n-1)/2`.
* `card_looplessClasses`, `card_looplessClasses_quot` — the loopless analogues
  (`fib(n-1) - (n-3)/2`).

## References

Severini — Theorem 12.
-/

namespace HessenbergDigraphs

open Finset Digraph

variable {n : ℕ}

section TotalCount

/-! ## Engineering layer — the value of a singleton active set as a plain `ℕ`
    (sum over the single element), used to form the singleton invariant. -/

/-- **Eng.** The total of the element values of `S` (equal to the unique value
when `S` is a singleton). -/
def sval (S : ActiveSet n) : ℕ := S.elements.sum Vertex.value

@[simp] theorem sval_singletonAs (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n - 1) :
    sval (singletonAs n t ht htn) = t := by
  simp [sval, singletonAs]

/-- **Eng.** A card-`1` active set is `singletonAs` of its element value. -/
theorem eq_singletonAs_of_card_one (S : ActiveSet n) (hS : S.elements.card = 1) :
    ∃ (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n - 1), S = singletonAs n t ht htn := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hS
  exact ⟨v.value, v.one_le_value, v.value_le_n, by
    apply ActiveSet.ext; rw [hv]; rfl⟩

/-! ## Mathematical layer — the complete isomorphism invariant. -/

/-- **Math.** A complete isomorphism invariant of `D_n(S)`: singletons map to
`min t (n - t)` (their iso class `{t, n - t}`), everything else maps to `S`. -/
def isoInvariant (S : ActiveSet n) : ℕ ⊕ ActiveSet n :=
  if S.elements.card = 1 then Sum.inl (min (sval S) (n - sval S)) else Sum.inr S

/-- **Math.** `D_n({t})` and `D_n({t'})` are isomorphic iff `{t, n-t} = {t', n-t'}`,
restated as `min t (n-t) = min t' (n-t')`. -/
theorem singleton_iso_iff_min (hn : 2 ≤ n) (t t' : ℕ) (ht : 1 ≤ t) (htn : t ≤ n - 1)
    (ht' : 1 ≤ t') (ht'n : t' ≤ n - 1) :
    (singletonAs n t ht htn).digraph ≅ (singletonAs n t' ht' ht'n).digraph ↔
      min t (n - t) = min t' (n - t') := by
  constructor
  · intro hiso
    have hpair := singleton_iso_unique n t t' hn ht htn ht' ht'n hiso
    -- {t, n-t} = {t', n-t'} as finsets ⟹ min equal
    have h1 : t ∈ ({t', n - t'} : Finset ℕ) := hpair ▸ (by simp)
    have h2 : n - t ∈ ({t', n - t'} : Finset ℕ) := hpair ▸ (by simp)
    have h3 : t' ∈ ({t, n - t} : Finset ℕ) := hpair ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3
    omega
  · intro hmin
    -- min equal ⟹ {t,n-t} = {t',n-t'} ⟹ t' = t or t' = n-t ⟹ iso
    have hcase : t' = t ∨ t' = n - t := by omega
    rcases hcase with h | h
    · subst h
      -- need (singletonAs t) ≅ (singletonAs t'); proofs may differ but t=t'
      exact isIsomorphicTo_refl _
    · subst h
      -- goal is exactly `D({t}) ≅ D({n-t})`, which is `singleton_iso`
      exact singleton_iso n t hn ht htn

/-! ## Mathematical layer — `isoInvariant` is a complete isomorphism invariant. -/

/-- **Math.** `isoInvariant` is a complete isomorphism invariant: two active sets
have the same invariant iff their digraphs are isomorphic. -/
theorem isoInvariant_eq_iff (S S' : ActiveSet n) (hn : 2 ≤ n) :
    isoInvariant S = isoInvariant S' ↔ S.digraph ≅ S'.digraph := by
  by_cases hS1 : S.elements.card = 1 <;> by_cases hS'1 : S'.elements.card = 1
  · -- both singletons
    obtain ⟨t, ht, htn, rfl⟩ := eq_singletonAs_of_card_one S hS1
    obtain ⟨t', ht', ht'n, rfl⟩ := eq_singletonAs_of_card_one S' hS'1
    unfold isoInvariant
    rw [if_pos hS1, if_pos hS'1]
    simp only [sval_singletonAs, Sum.inl.injEq]
    exact (singleton_iso_iff_min hn t t' ht htn ht' ht'n).symm
  · -- S singleton, S' not: invariants differ (inl ≠ inr); not isomorphic by iso_card_eq
    unfold isoInvariant
    rw [if_pos hS1, if_neg hS'1]
    constructor
    · intro h; simp at h
    · intro hiso
      have hcard := iso_card_eq S S' hn hiso
      rw [hS1] at hcard
      exact absurd hcard.symm hS'1
  · -- S not singleton, S' singleton (mirror)
    unfold isoInvariant
    rw [if_neg hS1, if_pos hS'1]
    constructor
    · intro h; simp at h
    · intro hiso
      have hcard := iso_card_eq S S' hn hiso
      rw [hS'1] at hcard
      exact absurd hcard hS1
  · -- both non-singletons: invariant is `Sum.inr S`, equal iff `S = S'`
    unfold isoInvariant
    rw [if_neg hS1, if_neg hS'1, Sum.inr.injEq]
    constructor
    · rintro rfl; exact isIsomorphicTo_refl _
    · intro hiso
      have hcard := iso_card_eq S S' hn hiso
      rcases Nat.lt_or_ge S.elements.card 2 with hlt | hge
      · -- |S| < 2 and ≠ 1 ⟹ |S| = 0 ⟹ both empty
        have hS0 : S.elements.card = 0 := by omega
        have hS'0 : S'.elements.card = 0 := by omega
        apply ActiveSet.ext
        rw [Finset.card_eq_zero.mp hS0, Finset.card_eq_zero.mp hS'0]
      · -- |S| ≥ 2 ⟹ |S'| ≥ 2 ⟹ rigid
        exact rigid S S' hn hge (by omega) hiso

/-! ## Mathematical layer — counting the strata. -/

/-- **Math.** There are exactly `n - 1` singleton active sets. -/
theorem card_singletons :
    (Finset.univ.filter (fun S : ActiveSet n => S.elements.card = 1)).card = n - 1 := by
  have hinj : Function.Injective (fun v : Vertex (n - 1) => (⟨{v}⟩ : ActiveSet n)) := by
    intro a b hab
    rw [ActiveSet.mk.injEq, Finset.singleton_inj] at hab
    exact hab
  have hset : (Finset.univ.filter (fun S : ActiveSet n => S.elements.card = 1))
      = Finset.univ.image (fun v : Vertex (n - 1) => (⟨{v}⟩ : ActiveSet n)) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hS
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hS
      exact ⟨v, by apply ActiveSet.ext; rw [hv]⟩
    · rintro ⟨v, rfl⟩
      simp
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Vertex.card_eq]

/-- **Math.** The singleton iso classes number `⌊n/2⌋`: the classes `{t, n-t}`
are indexed by `min t (n-t) ∈ {1, …, ⌊n/2⌋}`. -/
theorem card_singleton_classes (hn : 2 ≤ n) :
    ((Finset.univ.filter (fun S : ActiveSet n => S.elements.card = 1)).image
      (fun S => min (sval S) (n - sval S))).card = n / 2 := by
  have hset : (Finset.univ.filter (fun S : ActiveSet n => S.elements.card = 1)).image
      (fun S => min (sval S) (n - sval S)) = Finset.Icc 1 (n / 2) := by
    ext s
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
    constructor
    · rintro ⟨S, hScard, rfl⟩
      obtain ⟨t, ht, htn, rfl⟩ := eq_singletonAs_of_card_one S hScard
      rw [sval_singletonAs]
      omega
    · rintro ⟨hs1, hs2⟩
      refine ⟨singletonAs n s hs1 (by omega), by simp, ?_⟩
      rw [sval_singletonAs]
      omega
  rw [hset, Nat.card_Icc]
  omega

/-! ## Mathematical layer — Paper Theorem 12: the class count. -/

/-- **Math.** The number of isomorphism classes of `D_n(S)` (the distinct values
of the complete invariant `isoInvariant`) is `2^(n-1) - ⌊(n-1)/2⌋`. Paper:
Theorem 12. -/
theorem card_isoClasses (hn : 2 ≤ n) :
    ((Finset.univ : Finset (ActiveSet n)).image isoInvariant).card
      = 2 ^ (n - 1) - (n - 1) / 2 := by
  have himg_sing :
      (Finset.univ.filter (fun S : ActiveSet n => S.elements.card = 1)).image isoInvariant
      = ((Finset.univ.filter (fun S : ActiveSet n => S.elements.card = 1)).image
          (fun S => min (sval S) (n - sval S))).image Sum.inl := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    unfold isoInvariant
    rw [if_pos hS]
    rfl
  have himg_nonsing :
      (Finset.univ.filter (fun S : ActiveSet n => ¬ S.elements.card = 1)).image isoInvariant
      = (Finset.univ.filter (fun S : ActiveSet n => ¬ S.elements.card = 1)).image Sum.inr := by
    apply Finset.image_congr
    intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    unfold isoInvariant
    rw [if_neg hS]
  have hdisj : Disjoint
      (((Finset.univ.filter (fun S : ActiveSet n => S.elements.card = 1)).image
        (fun S => min (sval S) (n - sval S))).image Sum.inl)
      ((Finset.univ.filter (fun S : ActiveSet n => ¬ S.elements.card = 1)).image Sum.inr) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_image] at hx1 hx2
    obtain ⟨_, _, rfl⟩ := hx1
    obtain ⟨_, _, h⟩ := hx2
    exact Sum.inl_ne_inr h.symm
  have hnonsing :
      (Finset.univ.filter (fun S : ActiveSet n => ¬ S.elements.card = 1)).card
        = 2 ^ (n - 1) - (n - 1) := by
    have hadd := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ActiveSet n))) (fun S => S.elements.card = 1)
    rw [card_singletons, Finset.card_univ, ActiveSet.card_eq] at hadd
    omega
  rw [← Finset.filter_union_filter_not_eq (fun S : ActiveSet n => S.elements.card = 1)
        Finset.univ,
      Finset.image_union, himg_sing, himg_nonsing,
      Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective,
      card_singleton_classes hn, hnonsing]
  have hpow : n - 1 ≤ 2 ^ (n - 1) := Nat.le_of_lt (Nat.lt_two_pow_self)
  omega

/-! ## Mathematical layer — the count as the cardinality of the quotient by
    isomorphism: the directly readable form of Theorem 12. -/

/-- **Math.** Active sets up to support-digraph isomorphism: `S ≈ S'` iff
`D_n(S) ≅ D_n(S')`. -/
def isoSetoid (n : ℕ) : Setoid (ActiveSet n) where
  r S S' := S.digraph ≅ S'.digraph
  iseqv :=
    ⟨fun S => isIsomorphicTo_refl S.digraph,
     fun ⟨e⟩ => ⟨e.symm⟩,
     fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- **Math.** The number of isomorphism classes of the support digraphs `D_n(S)`,
`S ⊆ [n-1]`, is `2^(n-1) - ⌊(n-1)/2⌋`. Paper: Theorem 12. The readable form of
`card_isoClasses`: the quotient of active sets by digraph isomorphism has
exactly that many elements (`isoInvariant` is a complete invariant, so it
descends to an injection into its image). -/
theorem card_isoClasses_quot (hn : 2 ≤ n) :
    Nat.card (Quotient (isoSetoid n)) = 2 ^ (n - 1) - (n - 1) / 2 := by
  classical
  let g : Quotient (isoSetoid n) → ℕ ⊕ ActiveSet n :=
    Quotient.lift isoInvariant (fun S S' h => (isoInvariant_eq_iff S S' hn).mpr h)
  have hg : Function.Injective g := by
    intro x y hxy
    obtain ⟨S, rfl⟩ := Quotient.exists_rep x
    obtain ⟨S', rfl⟩ := Quotient.exists_rep y
    exact Quotient.sound ((isoInvariant_eq_iff S S' hn).mp hxy)
  have hrange : Set.range g = Set.range isoInvariant := by
    ext z
    simp only [Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨S, rfl⟩ := Quotient.exists_rep x
      exact ⟨S, rfl⟩
    · rintro ⟨S, rfl⟩
      exact ⟨⟦S⟧, rfl⟩
  have hset : ((Finset.univ.image isoInvariant : Finset (ℕ ⊕ ActiveSet n)) :
        Set (ℕ ⊕ ActiveSet n)) = Set.range isoInvariant := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [← Nat.card_range_of_injective hg, hrange, ← hset, Nat.card_coe_set_eq,
      Set.ncard_coe_finset, card_isoClasses hn]

end TotalCount

section LooplessCount

/-! ## Mathematical layer — loopless count (Paper Theorem 15). -/

/-- **Math.** `S` is a loopless active set: its values lie in `{2, …, n-2}` and
no two are consecutive. By `loopless_iff` this is exactly looplessness of
`D_n(S)`. -/
def IsLooplessSet (S : ActiveSet n) : Prop :=
  (∀ k ∈ S.elements, 2 ≤ k.value ∧ k.value ≤ n - 2) ∧ NoConsecutive S

instance : DecidablePred (fun S : ActiveSet n => IsLooplessSet S) := fun S => by
  unfold IsLooplessSet NoConsecutive; infer_instance

/-- **Math.** The loopless active sets number `fib(n-1)`: their value sets,
shifted down by `2`, are exactly the no-two-consecutive subsets of `{0,…,n-4}`
(`indepSubsets (n-3)`, counted by `count_indep_subsets`). -/
theorem card_looplessSets (hn : 3 ≤ n) :
    (Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).card = Nat.fib (n - 1) := by
  have jbound : ∀ (T : Finset ℕ), T ∈ indepSubsets (n - 3) → ∀ t ∈ T, t + 2 ≤ n - 1 := by
    intro T hT t ht
    have := Finset.mem_range.mp (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1 ht)
    omega
  have key : (Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).card
      = (indepSubsets (n - 3)).card := by
    apply Finset.card_bij'
      (fun (S : ActiveSet n) _ => S.elements.image (fun k => k.value - 2))
      (fun (T : Finset ℕ) (hT : T ∈ indepSubsets (n - 3)) =>
        (⟨T.attach.image (fun x =>
          (⟨x.1 + 2, Nat.le_add_left 1 (x.1 + 1), jbound T hT x.1 x.2⟩ : Vertex (n - 1)))⟩ :
          ActiveSet n))
    · -- left inverse : rebuild ∘ shift = id on loopless sets
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      obtain ⟨hb, _⟩ := hS
      apply ActiveSet.ext
      ext k
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      constructor
      · rintro ⟨a, ⟨k0, hk0, rfl⟩, rfl⟩
        have := hb k0 hk0
        have hk0' : (⟨k0.value - 2 + 2, Nat.le_add_left 1 (k0.value - 2 + 1),
            by omega⟩ : Vertex (n - 1)) = k0 := by
          apply Vertex.ext; change k0.value - 2 + 2 = k0.value; omega
        rw [hk0']; exact hk0
      · intro hk
        have := hb k hk
        refine ⟨k.value - 2, ⟨k, hk, rfl⟩, ?_⟩
        apply Vertex.ext; change k.value - 2 + 2 = k.value; omega
    · -- right inverse : shift ∘ rebuild = id on `indepSubsets`
      intro T hT
      simp only [indepSubsets, Finset.mem_filter, Finset.mem_powerset] at hT
      obtain ⟨hTsub, _⟩ := hT
      ext a
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      constructor
      · rintro ⟨v, ⟨t, ht, rfl⟩, rfl⟩
        change t + 2 - 2 ∈ T
        rwa [Nat.add_sub_cancel]
      · intro ha
        have := Finset.mem_range.mp (hTsub ha)
        exact ⟨⟨a + 2, Nat.le_add_left 1 (a + 1), by omega⟩,
          ⟨a, ha, rfl⟩, by change a + 2 - 2 = a; omega⟩
    · -- hi : the shifted value set is in `indepSubsets (n-3)`
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      obtain ⟨hb, hnc⟩ := hS
      simp only [indepSubsets, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun a ha => ?_, fun a ha hcon => ?_⟩
      · rw [Finset.mem_image] at ha
        obtain ⟨k, hk, rfl⟩ := ha
        rw [Finset.mem_range]; have := hb k hk; omega
      · rw [Finset.mem_image] at ha hcon
        obtain ⟨k, hk, hka⟩ := ha
        obtain ⟨k', hk', hk'a⟩ := hcon
        have := hb k hk; have := hb k' hk'
        exact hnc k k' hk hk' (by omega)
    · -- hj : the rebuilt active set is loopless
      intro T hT
      simp only [indepSubsets, Finset.mem_filter, Finset.mem_powerset] at hT
      obtain ⟨hTsub, hTnc⟩ := hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun k hk => ?_, fun k k' hk hk' hcon => ?_⟩
      · rw [Finset.mem_image] at hk
        obtain ⟨x, _, rfl⟩ := hk
        have := Finset.mem_range.mp (hTsub x.2)
        exact ⟨Nat.le_add_left 2 x.1, by change x.1 + 2 ≤ n - 2; omega⟩
      · rw [Finset.mem_image] at hk hk'
        obtain ⟨x, _, rfl⟩ := hk
        obtain ⟨x', _, rfl⟩ := hk'
        have hxx : x.1 + 1 = x'.1 := by
          have h2 : x.1 + 2 + 1 = x'.1 + 2 := hcon
          omega
        exact hTnc x.1 x.2 (hxx ▸ x'.2)
  rw [key, count_indep_subsets]
  congr 1
  omega

/-- **Math.** A singleton `{t}` is loopless iff `2 ≤ t ≤ n - 2`. -/
theorem isLooplessSet_singletonAs (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n - 1) :
    IsLooplessSet (singletonAs n t ht htn) ↔ 2 ≤ t ∧ t ≤ n - 2 := by
  simp only [IsLooplessSet, NoConsecutive, singletonAs_elements, Finset.mem_singleton, forall_eq]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rintro k k' rfl rfl
  omega

/-- **Math.** There are exactly `n - 3` loopless singleton active sets (one for
each value `t ∈ {2, …, n-2}`). -/
theorem card_loopless_singletons (hn : 3 ≤ n) :
    ((Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).filter
      (fun S => S.elements.card = 1)).card = n - 3 := by
  set X := (Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).filter
    (fun S => S.elements.card = 1) with hX
  have hinj : Set.InjOn sval (X : Set (ActiveSet n)) := by
    intro S hS S' hS' he
    simp only [hX, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS hS'
    obtain ⟨t, ht, htn, rfl⟩ := eq_singletonAs_of_card_one S hS.2
    obtain ⟨t', ht', ht'n, rfl⟩ := eq_singletonAs_of_card_one S' hS'.2
    rw [sval_singletonAs, sval_singletonAs] at he
    subst he; rfl
  have hset : X.image sval = Finset.Icc 2 (n - 2) := by
    rw [hX]; ext s
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
    constructor
    · rintro ⟨S, ⟨hLp, hc⟩, rfl⟩
      obtain ⟨t, ht, htn, rfl⟩ := eq_singletonAs_of_card_one S hc
      rw [sval_singletonAs]
      exact (isLooplessSet_singletonAs t ht htn).mp hLp
    · rintro ⟨hs2, hsn⟩
      exact ⟨singletonAs n s (by omega) (by omega),
        ⟨(isLooplessSet_singletonAs s (by omega) (by omega)).mpr ⟨hs2, hsn⟩, by simp⟩,
        by rw [sval_singletonAs]⟩
  rw [← Finset.card_image_of_injOn hinj, hset, Nat.card_Icc]
  omega

/-- **Math.** The loopless singleton iso classes number `⌊n/2⌋ - 1`: the classes
`{t, n-t}` with `t ∈ {2,…,n-2}` are indexed by `min t (n-t) ∈ {2,…,⌊n/2⌋}`. -/
theorem card_loopless_singleton_classes (hn : 3 ≤ n) :
    (((Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).filter
      (fun S => S.elements.card = 1)).image (fun S => min (sval S) (n - sval S))).card
      = n / 2 - 1 := by
  have hset : (((Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).filter
      (fun S => S.elements.card = 1)).image (fun S => min (sval S) (n - sval S)))
      = Finset.Icc 2 (n / 2) := by
    ext s
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
    constructor
    · rintro ⟨S, ⟨hLp, hc⟩, rfl⟩
      obtain ⟨t, ht, htn, rfl⟩ := eq_singletonAs_of_card_one S hc
      rw [sval_singletonAs]
      have := (isLooplessSet_singletonAs t ht htn).mp hLp
      omega
    · rintro ⟨hs2, hsn⟩
      refine ⟨singletonAs n s (by omega) (by omega),
        ⟨(isLooplessSet_singletonAs s (by omega) (by omega)).mpr ⟨hs2, by omega⟩, by simp⟩, ?_⟩
      rw [sval_singletonAs]; omega
  rw [hset, Nat.card_Icc]
  omega

/-! ## Mathematical layer — Paper Theorem 15: the loopless class count. -/

/-- **Math.** The number of loopless isomorphism classes of `D_n(S)` is
`fib(n-1) - ⌊(n-3)/2⌋`. Paper: Theorem 15. The `fib` lower bound `hfib` is the
same side condition carried by `count_loopless_formula`. -/
theorem card_looplessClasses (hn : 3 ≤ n) (hfib : n - 3 + 1 ≤ Nat.fib (n - 1)) :
    ((Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).image isoInvariant).card
      = Nat.fib (n - 1) - (n - 3) / 2 := by
  have himg_sing :
      ((Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).filter
        (fun S => S.elements.card = 1)).image isoInvariant
      = (((Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).filter
          (fun S => S.elements.card = 1)).image
          (fun S => min (sval S) (n - sval S))).image Sum.inl := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter] at hS
    unfold isoInvariant
    rw [if_pos hS.2]
    rfl
  have himg_nonsing :
      ((Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).filter
        (fun S => ¬ S.elements.card = 1)).image isoInvariant
      = ((Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).filter
          (fun S => ¬ S.elements.card = 1)).image Sum.inr := by
    apply Finset.image_congr
    intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter] at hS
    unfold isoInvariant
    rw [if_neg hS.2]
  have hdisj : Disjoint
      ((((Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).filter
        (fun S => S.elements.card = 1)).image
        (fun S => min (sval S) (n - sval S))).image Sum.inl)
      (((Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).filter
        (fun S => ¬ S.elements.card = 1)).image Sum.inr) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_image] at hx1 hx2
    obtain ⟨_, _, rfl⟩ := hx1
    obtain ⟨_, _, h⟩ := hx2
    exact Sum.inl_ne_inr h.symm
  have hns :
      ((Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).filter
        (fun S => ¬ S.elements.card = 1)).card = Nat.fib (n - 1) - (n - 3) := by
    have hadd := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S))
      (fun S => S.elements.card = 1)
    rw [card_loopless_singletons hn, card_looplessSets hn] at hadd
    omega
  rw [← Finset.filter_union_filter_not_eq (fun S : ActiveSet n => S.elements.card = 1)
        (Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)),
      Finset.image_union, himg_sing, himg_nonsing,
      Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective,
      card_loopless_singleton_classes hn, hns]
  omega

/-! ## Mathematical layer — the loopless count as a quotient cardinality. -/

/-- **Math.** Loopless active sets up to support-digraph isomorphism. -/
def looplessIsoSetoid (n : ℕ) : Setoid {S : ActiveSet n // IsLooplessSet S} where
  r S S' := S.val.digraph ≅ S'.val.digraph
  iseqv :=
    ⟨fun S => isIsomorphicTo_refl S.val.digraph,
     fun ⟨e⟩ => ⟨e.symm⟩,
     fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- **Math.** The number of isomorphism classes of the loopless support digraphs
`D_n(S)` is `fib(n-1) - ⌊(n-3)/2⌋`. Paper: Theorem 15. The readable form of
`card_looplessClasses`. -/
theorem card_looplessClasses_quot (hn : 3 ≤ n) (hfib : n - 3 + 1 ≤ Nat.fib (n - 1)) :
    Nat.card (Quotient (looplessIsoSetoid n)) = Nat.fib (n - 1) - (n - 3) / 2 := by
  classical
  let g : Quotient (looplessIsoSetoid n) → ℕ ⊕ ActiveSet n :=
    Quotient.lift (fun S => isoInvariant S.val)
      (fun S S' h => (isoInvariant_eq_iff S.val S'.val (by omega)).mpr h)
  have hg : Function.Injective g := by
    intro x y hxy
    obtain ⟨S, rfl⟩ := Quotient.exists_rep x
    obtain ⟨S', rfl⟩ := Quotient.exists_rep y
    exact Quotient.sound ((isoInvariant_eq_iff S.val S'.val (by omega)).mp hxy)
  have hset : (((Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).image
        isoInvariant : Finset (ℕ ⊕ ActiveSet n)) : Set (ℕ ⊕ ActiveSet n))
      = Set.range g := by
    ext z
    simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨⟦⟨S, hS⟩⟧, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨⟨S, hS⟩, rfl⟩ := Quotient.exists_rep x
      exact ⟨S, hS, rfl⟩
  rw [← Nat.card_range_of_injective hg, ← hset, Nat.card_coe_set_eq,
      Set.ncard_coe_finset, card_looplessClasses hn hfib]

end LooplessCount

end HessenbergDigraphs
