/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Combinatorial.Arc
import HessenbergDigraphs.Vertex
import HessenbergDigraphs.ActiveSet

/-!
# Directed Hamilton cycle in `D_n(S)`

Every `D_n(S)` contains the directed Hamilton cycle
`H : 1 → n → (n - 1) → ⋯ → 2 → 1` regardless of `S`. Migrated to
bundled-structure API: `S : ActiveSet n`, vertices in `Vertex n`, arcs via
the inductive `Arc S i j`.

## Main results

* `HCycleArc n i j` — predicate isolating the arcs of `H`.
* `hcycle_subset` — every arc of `H` is an arc of `D_n(S)`
  (Paper: Lemma 8).

## References

Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" —
Lemma 8.
-/

namespace HessenbergDigraphs

variable (n : ℕ)

/-! ## Mathematical layer — Lean-side definition (Hamilton-cycle arc
    predicate over `Vertex n`). -/

/-- **Math.** The directed Hamilton cycle's arc relation: either `(1, n)` or
    `(i, i - 1)` for `2 ≤ i ≤ n`. -/
def HCycleArc (i j : Vertex n) : Prop :=
  (i.value = 1 ∧ j.value = n) ∨ (2 ≤ i.value ∧ j.value = i.value - 1)

/-! ## Mixed — Math: Paper Lemma 8 (Hamilton ⊆ D_n(S)) — the disjoint
    overlay-then-spine matching of `HCycleArc`'s two branches against
    `Arc.overlay` / `Arc.spine`. | Eng: under the bundled-structure API the spine
    construction folds into `Vertex.next`. -/

/-- **Mixed.** Every arc of the directed Hamilton cycle is an arc of `D_n(S)`,
regardless of `S`. Paper: Lemma 8. -/
theorem hcycle_subset (S : ActiveSet n) (hn : 2 ≤ n) :
    ∀ i j : Vertex n, HCycleArc n i j → Arc S i j := by
  intro i j H
  rcases H with ⟨hi_eq, hj_eq⟩ | ⟨hi_ge, hj_eq⟩
  · -- (1, n): overlay arc
    have hn1 : 1 ≤ n := by omega
    have hi_eq' : i = Vertex.first hn1 := by ext; exact hi_eq
    have hj_eq' : j = Vertex.last hn1 := by ext; exact hj_eq
    rw [hi_eq', hj_eq']
    exact Arc.overlay _ _ (ActiveSet.first_mem_activeRows hn1 S)
      (ActiveSet.last_mem_activeCols hn1 S)
      (by change (Vertex.first hn1).value ≤ (Vertex.last hn1).value
          change 1 ≤ n; omega)
  · -- (i, i - 1) for 2 ≤ i ≤ n: spine arc
    have h : j.value < n := by
      have := i.value_le_n
      omega
    have hi_eq' : i = j.next h := by
      ext
      change i.value = j.value + 1
      omega
    rw [hi_eq']
    exact Arc.spine j h

end HessenbergDigraphs
