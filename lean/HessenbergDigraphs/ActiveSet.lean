/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import HessenbergDigraphs.Vertex
import HessenbergDigraphs.Combinatorial.Digraph

/-!
# ActiveSet: paper-side `S ⊆ [n - 1]` active sets

`ActiveSet n` is a `Finset` of `Vertex (n - 1)` — exactly the paper's
`S ⊆ {1, …, n - 1}`. The `Vertex (n - 1)` element type carries the
`1 ≤ k ≤ n - 1` bound automatically, eliminating the legacy
`ValidActiveSet n S : ∀ k ∈ S, 1 ≤ k ∧ k ≤ n - 1` side condition that
every downstream proof has had to thread through.

This file introduces:

* the `ActiveSet n` structure;
* a `values` / `fromValues` bridge to/from `Finset ℕ` (for migration
  while existing files still take `Finset ℕ`);
* the paper-side derived sets `activeRows S : Finset (Vertex n)` and
  `activeCols S : Finset (Vertex n)`;
* the principal map `S.digraph : Digraph n` matching the paper's
  `D_n(S)` arc relation.

## Main definitions

* `ActiveSet n` — structure with `elements : Finset (Vertex (n - 1))`.
* `ActiveSet.values` / `ActiveSet.fromValues` — bridge to/from
  `Finset ℕ` for migration.
* `ActiveSet.activeRows`, `ActiveSet.activeCols` — paper's derived sets,
  living in `Finset (Vertex n)` (one bound up from `Vertex (n - 1)`).
* `ActiveSet.digraph` — paper's `D_n(S)` as a `Digraph n`.

## Implementation notes

* The `elements` field uses `Finset (Vertex (n - 1))` (not `Finset ℕ`
  + validity predicate), so the bound is enforced by the type. For
  `n = 0` and `n = 1`, `Vertex (n - 1)` is empty, so the only `ActiveSet`
  is empty — matching the paper's vacuous treatment of those cases.
* `activeRows` / `activeCols` produce `Finset (Vertex n)` by lifting
  active-set elements: active rows shift the value up by one (`k ↦ k + 1`,
  via an explicit `Vertex` constructor), active columns include by
  preserving the value (`Vertex.castGE`, the identity inclusion
  `Vertex (n - 1) ↪ Vertex n`).
* `digraph` writes the spine arc as `i = j.next h` (using `Vertex.next`)
  rather than the legacy `i.val = j.val + 1` plumbing.

## References

Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" — §0,
Theorem 7.
-/

namespace HessenbergDigraphs

/-! ## Mathematical layer — paper-side active set type. `ActiveSet n` is
    a `Finset` of `Vertex (n - 1)`; the bound `1 ≤ k ≤ n - 1` is carried
    by the element type. -/

/-- **Math.** A paper-side active set: `S ⊆ {1, …, n - 1}`, encoded as a `Finset`
of `Vertex (n - 1)` so the bound is type-level. -/
@[ext]
structure ActiveSet (n : ℕ) where
  elements : Finset (Vertex (n - 1))
  deriving DecidableEq

namespace ActiveSet

variable {n : ℕ}

/-! ### Bridges to `Finset ℕ` (migration glue) -/

/-! ## Engineering layer — Type B bridge to legacy `Finset ℕ` callers.
    `values` extracts the underlying paper-side `ℕ` values; `fromValues`
    builds an `ActiveSet` from a `Finset ℕ` plus the bound-side condition
    that the legacy `ValidActiveSet` predicate carries. -/

/-- **Eng.** The underlying paper-side `Finset ℕ` of values. -/
def values (S : ActiveSet n) : Finset ℕ := S.elements.image Vertex.value

/-- **Eng.** Build an `ActiveSet n` from a `Finset ℕ` of paper-side values plus
the legacy bound condition `1 ≤ k ≤ n - 1`. -/
def fromValues (T : Finset ℕ) (hT : ∀ k ∈ T, 1 ≤ k ∧ k ≤ n - 1) :
    ActiveSet n where
  elements := T.attach.image
    (fun ⟨k, hk⟩ =>
      ({ value := k
         one_le_value := (hT k hk).1
         value_le_n := (hT k hk).2 } : Vertex (n - 1)))

/-! ### Basic API -/

/-! ## Mathematical layer — basic cardinality. -/

/-- **Math.** The cardinality of the active set. -/
def card (S : ActiveSet n) : ℕ := S.elements.card

/-! ### Finiteness -/

/-! ## Engineering layer — Type B: `ActiveSet n` is its single field
    `Finset (Vertex (n - 1))`, hence finite with `2 ^ (n - 1)` elements
    (one per subset `S ⊆ [n - 1]`). -/

/-- **Eng.** `ActiveSet n` is equivalent to its underlying `Finset (Vertex (n - 1))`. -/
def equivFinset : ActiveSet n ≃ Finset (Vertex (n - 1)) where
  toFun := elements
  invFun := mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance instFintype : Fintype (ActiveSet n) := Fintype.ofEquiv _ equivFinset.symm

/-- **Math.** There are exactly `2 ^ (n - 1)` active sets `S ⊆ [n - 1]`. -/
theorem card_eq (n : ℕ) : Fintype.card (ActiveSet n) = 2 ^ (n - 1) := by
  rw [Fintype.card_congr (equivFinset (n := n)), Fintype.card_finset, Vertex.card_eq]

/-! ### Paper-side derived sets -/

/-! ## Mathematical layer — Paper Theorem 7 derived sets. `activeRows`
    is `{1} ∪ {k + 1 | k ∈ S}`; `activeCols` is `S ∪ {n}`. Both produce
    `Finset (Vertex n)` (one dimension up from the active-set element
    type). The shifts are encoded via the explicit `Vertex` constructor
    (for the `+ 1` shift in `activeRows`) and `Vertex.castGE` (for the
    identity inclusion in `activeCols`). -/

/-- **Math.** Paper-side `activeRows(S) = {1} ∪ {k + 1 | k ∈ S}`. The `1`
contribution requires `1 ≤ n` (otherwise vacuous). -/
def activeRows (S : ActiveSet n) : Finset (Vertex n) :=
  (if h : 1 ≤ n then ({Vertex.first h} : Finset _) else ∅) ∪
  S.elements.image
    (fun k =>
      ({ value := k.value + 1
         one_le_value := by have := k.one_le_value; omega
         value_le_n := by
           have h1 := k.one_le_value
           have h2 := k.value_le_n
           omega } : Vertex n))

/-- **Math.** Paper-side `activeCols(S) = S ∪ {n}`. The `n` contribution requires
`1 ≤ n` (otherwise vacuous). -/
def activeCols (S : ActiveSet n) : Finset (Vertex n) :=
  S.elements.image (Vertex.castGE (Nat.sub_le n 1)) ∪
  (if h : 1 ≤ n then ({Vertex.last h} : Finset _) else ∅)

/-! ## Mathematical layer — paper-side membership characterisation: `v` is
    in `S.activeRows` iff `v` is the first vertex (`v.value = 1`) or `v`
    is the successor of some `k ∈ S.elements` (`k.value + 1 = v.value`). -/

/-- **Math.** Membership in `S.activeRows`: either `v.value = 1` or `v` is the
successor of some `k ∈ S.elements`. -/
@[simp] theorem mem_activeRows_iff (S : ActiveSet n) (v : Vertex n) :
    v ∈ S.activeRows ↔
      v.value = 1 ∨ ∃ k ∈ S.elements, k.value + 1 = v.value := by
  unfold activeRows
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h_first | ⟨k, hkS, hk_eq⟩)
    · left
      split_ifs at h_first with hn
      · simp only [Finset.mem_singleton] at h_first
        rw [h_first]; rfl
      · simp at h_first
    · right; refine ⟨k, hkS, ?_⟩
      have := congrArg Vertex.value hk_eq
      simpa using this
  · rintro (h_eq | ⟨k, hkS, hk_eq⟩)
    · left
      have hn : 1 ≤ n := by have := v.value_le_n; omega
      simp only [hn, dif_pos, Finset.mem_singleton]
      ext
      change v.value = 1
      exact h_eq
    · right; exact ⟨k, hkS, by ext; change k.value + 1 = v.value; exact hk_eq⟩

/-! ## Mathematical layer — paper-side membership characterisation: `v` is
    in `S.activeCols` iff `v` agrees in value with some `k ∈ S.elements`
    or `v` is the last vertex (`v.value = n`). -/

/-- **Math.** Membership in `S.activeCols`: either `v` matches some `k ∈ S.elements`
in value, or `v.value = n`. -/
@[simp] theorem mem_activeCols_iff (S : ActiveSet n) (v : Vertex n) :
    v ∈ S.activeCols ↔
      (∃ k ∈ S.elements, k.value = v.value) ∨ v.value = n := by
  unfold activeCols
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨k, hkS, hk_eq⟩ | h_last)
    · left; refine ⟨k, hkS, ?_⟩
      have := congrArg Vertex.value hk_eq
      simpa [Vertex.castGE] using this
    · right
      split_ifs at h_last with hn
      · simp only [Finset.mem_singleton] at h_last
        rw [h_last]; rfl
      · simp at h_last
  · rintro (⟨k, hkS, hk_eq⟩ | h_eq)
    · left; refine ⟨k, hkS, ?_⟩; ext; exact hk_eq
    · right
      have hn : 1 ≤ n := by have := v.one_le_value; omega
      simp only [hn, dif_pos, Finset.mem_singleton]
      ext
      change v.value = n
      exact h_eq

/-! ## Mathematical layer — paper-side closure facts. -/

/-- **Math.** The first vertex is always in `S.activeRows` (when `1 ≤ n`). -/
@[simp] theorem first_mem_activeRows (h : 1 ≤ n) (S : ActiveSet n) :
    Vertex.first h ∈ S.activeRows := by
  rw [mem_activeRows_iff]; left; rfl

/-- **Math.** The last vertex is always in `S.activeCols` (when `1 ≤ n`). -/
@[simp] theorem last_mem_activeCols (h : 1 ≤ n) (S : ActiveSet n) :
    Vertex.last h ∈ S.activeCols := by
  rw [mem_activeCols_iff]; right; rfl

/-! ## Mathematical layer — `|activeRows S| = |S| + 1` (the `{1}` contribution
    plus the `k ↦ k + 1` image of `S`, disjoint and injective). -/

/-- **Math.** `activeRows(S)` has exactly `|S| + 1` elements. -/
theorem card_activeRows (S : ActiveSet n) (hn : 1 ≤ n) :
    S.activeRows.card = S.elements.card + 1 := by
  unfold activeRows
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ ?_]
  · rw [dif_pos hn, Finset.card_singleton]; omega
  · intro a b hab
    ext
    have h : a.value + 1 = b.value + 1 := congrArg Vertex.value hab
    omega
  · rw [Finset.disjoint_left]
    intro x hxL hxR
    rw [dif_pos hn, Finset.mem_singleton] at hxL
    simp only [Finset.mem_image] at hxR
    obtain ⟨k, _, hk_eq⟩ := hxR
    have hxv : x.value = 1 := by rw [hxL]; rfl
    have hk_value : k.value + 1 = x.value := congrArg Vertex.value hk_eq
    have := k.one_le_value
    omega

/-! ## Mathematical layer — spine successor of an active column lands in the
    active rows: `v ∈ activeCols`, `v` not last `⟹ v.next ∈ activeRows`. Used
    in the in-degree upper bound. -/

/-- **Math.** If `v ∈ activeCols(S)` and `v.value < n`, then `v.next` lies in
`activeRows(S)`. -/
theorem next_mem_activeRows (S : ActiveSet n) (v : Vertex n)
    (hv : v ∈ S.activeCols) (h : v.value < n) : v.next h ∈ S.activeRows := by
  rw [mem_activeRows_iff]
  rcases (mem_activeCols_iff S v).mp hv with ⟨k, hkS, hk_eq⟩ | hvn
  · right
    refine ⟨k, hkS, ?_⟩
    change k.value + 1 = v.value + 1
    rw [hk_eq]
  · exact absurd hvn (by omega)

/-! ### Principal arc relation -/

/-! ## Mathematical layer — Paper Theorem 7 arc relation `D_n(S)` as a
    `Digraph n`. Two disjuncts:

    * **spine**: `i = j.next h` for some `h : j.value < n`. The
      `Vertex.next` form replaces the legacy `i.val = j.val + 1 ∧ …`
      conjunction.
    * **overlay**: `i ∈ activeRows S`, `j ∈ activeCols S`, `i ≤ j`
      (using `Vertex.LE`).

    Compared to the inductive `Combinatorial.Arc` (which
    takes raw ℕ and threads three explicit bound conditions per
    constructor), the spine bound `1 ≤ j.value` collapses (carried by
    `Vertex`), and the `j.value + 1 ≤ n` condition becomes the
    transparent `j.value < n`. -/

/-- **Math.** The paper's arc relation `D_n(S)` as a `Digraph n`. -/
def digraph (S : ActiveSet n) : Digraph n :=
  fun i j =>
    (∃ h : j.value < n, i = j.next h) ∨
    (i ∈ S.activeRows ∧ j ∈ S.activeCols ∧ i ≤ j)

end ActiveSet

/-! ## Mathematical layer — Paper Corollary 14 condition. -/

/-- **Math.** `S` has no two consecutive elements: no `k, k' ∈ S` satisfy
`k.value + 1 = k'.value`. Used in the loopless characterisation
(Paper: Corollary 14). -/
def NoConsecutive {n : ℕ} (S : ActiveSet n) : Prop :=
  ∀ k k' : Vertex (n - 1), k ∈ S.elements → k' ∈ S.elements →
    k.value + 1 ≠ k'.value

end HessenbergDigraphs
