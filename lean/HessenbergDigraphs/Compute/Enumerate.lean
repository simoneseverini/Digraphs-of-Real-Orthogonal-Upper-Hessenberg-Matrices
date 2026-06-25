/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import HessenbergDigraphs.Combinatorial.Arc
import HessenbergDigraphs.Compute.Repr

/-!
# Computable arc and loop enumeration

Certified enumeration functions for the arcs and loops of `D_n(S)`.

## Main definitions

* `ActiveSet.arcList` — all arcs as a list of `(source, target)` pairs.
* `ActiveSet.spineArcList` — spine arcs only.
* `ActiveSet.overlayArcList` — overlay arcs only.
* `ActiveSet.loopVertices` — vertices carrying a self-loop.
-/

namespace HessenbergDigraphs

open Finset

variable {n : ℕ}

private def allVertices (n : ℕ) : List (Vertex n) :=
  (List.finRange n).map Vertex.ofFin

/-- **Eng.** All arcs of `D_n(S)` as a list of `(source, target)` value
pairs, ordered by source then target. -/
def ActiveSet.arcList (S : ActiveSet n) : List (ℕ × ℕ) :=
  let vs := allVertices n
  vs.flatMap (fun i =>
    (vs.filter (fun j => decide (Arc S i j))).map
      (fun j => (i.value, j.value)))

/-- **Eng.** Spine arcs on `n` vertices as value pairs. Independent of `S`. -/
def spineArcs (n : ℕ) : List (ℕ × ℕ) :=
  let vs := allVertices n
  vs.flatMap (fun i =>
    (vs.filter (fun j =>
      decide (∃ h : j.value < n, i = j.next h))).map
      (fun j => (i.value, j.value)))

/-- **Eng.** Spine arcs of `D_n(S)`. Delegates to `spineArcs n`. -/
def ActiveSet.spineArcList (S : ActiveSet n) : List (ℕ × ℕ) :=
  spineArcs n

/-- **Eng.** Overlay arcs of `D_n(S)` as value pairs. -/
def ActiveSet.overlayArcList (S : ActiveSet n) : List (ℕ × ℕ) :=
  let vs := allVertices n
  vs.flatMap (fun i =>
    (vs.filter (fun j =>
      decide (i ∈ S.activeRows ∧ j ∈ S.activeCols ∧ i ≤ j))).map
      (fun j => (i.value, j.value)))

/-- **Eng.** Vertices carrying a self-loop in `D_n(S)`, as sorted values. -/
def ActiveSet.loopVertices (S : ActiveSet n) : List ℕ :=
  (allVertices n).filterMap (fun v =>
    if decide (Arc S v v) then some v.value else none)

/-! ## Mathematical layer — specification of the enumerators. Each computed
    list contains exactly the value-pairs of the corresponding formal
    relation, characterised below as `↔`. These are the correctness
    theorems that turn the rendered digraph into a faithful image of the
    formal `Arc` / spine / overlay relations rather than a parallel
    re-implementation: the widget displays `arcList`, and `mem_arcList_iff`
    proves `arcList` is exactly `Arc`. -/

/-- **Eng.** Enumeration completeness: every vertex occurs in `allVertices n`. -/
private theorem mem_allVertices (v : Vertex n) : v ∈ allVertices n := by
  unfold allVertices
  rw [List.mem_map]
  exact ⟨v.toFin, List.mem_finRange _, Vertex.ofFin_toFin v⟩

/-- **Math.** `arcList` enumerates exactly the arcs of `D_n(S)`: a value-pair
`(a, b)` occurs iff it is `(i.value, j.value)` for vertices with `Arc S i j`. -/
theorem mem_arcList_iff (S : ActiveSet n) (a b : ℕ) :
    (a, b) ∈ S.arcList ↔ ∃ i j : Vertex n, i.value = a ∧ j.value = b ∧ Arc S i j := by
  simp only [ActiveSet.arcList, List.mem_flatMap, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨i, _, j, ⟨_, harc⟩, rfl, rfl⟩
    exact ⟨i, j, rfl, rfl, harc⟩
  · rintro ⟨i, j, rfl, rfl, harc⟩
    exact ⟨i, mem_allVertices i, j, ⟨mem_allVertices j, harc⟩, rfl, rfl⟩

/-- **Math.** End-to-end specification: the rendered arc list is exactly the
paper's digraph `D_n(S)`. `(a, b) ∈ S.arcList` iff `(a, b)` is a vertex
value-pair `(i, j)` with `S.digraph i j`. Composes `mem_arcList_iff` with
`arc_iff_digraph`, tying the calculator's output to the classified object. -/
theorem mem_arcList_iff_digraph (S : ActiveSet n) (a b : ℕ) :
    (a, b) ∈ S.arcList ↔
      ∃ i j : Vertex n, i.value = a ∧ j.value = b ∧ S.digraph i j := by
  simp only [mem_arcList_iff, arc_iff_digraph]

/-- **Math.** `spineArcList` enumerates exactly the spine arcs `j.next h → j`. -/
theorem mem_spineArcList_iff (S : ActiveSet n) (a b : ℕ) :
    (a, b) ∈ S.spineArcList ↔
      ∃ i j : Vertex n, i.value = a ∧ j.value = b ∧ ∃ h : j.value < n, i = j.next h := by
  simp only [ActiveSet.spineArcList, spineArcs, List.mem_flatMap, List.mem_map,
    List.mem_filter, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨i, _, j, ⟨_, hsp⟩, rfl, rfl⟩
    exact ⟨i, j, rfl, rfl, hsp⟩
  · rintro ⟨i, j, rfl, rfl, hsp⟩
    exact ⟨i, mem_allVertices i, j, ⟨mem_allVertices j, hsp⟩, rfl, rfl⟩

/-- **Math.** `overlayArcList` enumerates exactly the overlay arcs of `D_n(S)`. -/
theorem mem_overlayArcList_iff (S : ActiveSet n) (a b : ℕ) :
    (a, b) ∈ S.overlayArcList ↔
      ∃ i j : Vertex n, i.value = a ∧ j.value = b ∧
        i ∈ S.activeRows ∧ j ∈ S.activeCols ∧ i ≤ j := by
  simp only [ActiveSet.overlayArcList, List.mem_flatMap, List.mem_map,
    List.mem_filter, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨i, _, j, ⟨_, hov⟩, rfl, rfl⟩
    exact ⟨i, j, rfl, rfl, hov⟩
  · rintro ⟨i, j, rfl, rfl, hov⟩
    exact ⟨i, mem_allVertices i, j, ⟨mem_allVertices j, hov⟩, rfl, rfl⟩

/-- **Math.** `loopVertices` enumerates exactly the self-loop vertices:
`a ∈ S.loopVertices` iff `a = v.value` for some `v` with a loop `Arc S v v`. -/
theorem mem_loopVertices_iff (S : ActiveSet n) (a : ℕ) :
    a ∈ S.loopVertices ↔ ∃ v : Vertex n, v.value = a ∧ Arc S v v := by
  simp only [ActiveSet.loopVertices, List.mem_filterMap]
  constructor
  · rintro ⟨v, _, hv⟩
    split_ifs at hv with harc
    simp only [Option.some.injEq] at hv
    exact ⟨v, hv, of_decide_eq_true harc⟩
  · rintro ⟨v, rfl, harc⟩
    exact ⟨v, mem_allVertices v, by simp [harc]⟩

end HessenbergDigraphs
