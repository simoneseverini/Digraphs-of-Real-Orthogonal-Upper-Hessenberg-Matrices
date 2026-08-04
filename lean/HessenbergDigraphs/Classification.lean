/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Combinatorial.Rigidity
import HessenbergDigraphs.Realization.DigraphModel
import HessenbergDigraphs.Matrix.UnreducedAngles

/-!
# The classification trinity

The classification of support digraphs of unreduced real orthogonal upper
Hessenberg matrices is **not a single theorem**: it is the conjunction of
three independent statements, each proved in its appropriate layer of the
library.

* `completeness` (`Realization.DigraphModel`) — every `S : ActiveSet n` is
  realized as `θ.activeSet` for some `θ : UnreducedAngles n`.
* `digraph_model` (`Realization.DigraphModel`) — for every
  `θ : UnreducedAngles n`, the support of `θ.product` agrees with
  `θ.activeSet.digraph` arc-for-arc.
* `rigid` (`Combinatorial.Rigidity`) — for `|S|, |S'| ≥ 2`,
  `S.digraph ≅ S'.digraph` forces `S = S'`.

The paper presents these together as Theorem 1. The `classification`
declaration in this file packages them into a single triple — purely as a
citation handle. It introduces no new mathematical content. Code that
needs any one component should call that component directly rather than
destructuring `classification`.

## References

Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" — Theorem 1.
-/

namespace HessenbergDigraphs

open Matrix Finset Digraph

/-! ## Mathematical layer — Paper: Theorem 1 (apex classification).
    Term-level packaging of the three independently-proved components:
    `completeness` (realizability), `digraph_model` (matrix-side ↔
    combinatorial-side support equivalence), and `rigid` (automorphism
    rigidity for `|S| ≥ 2`). All three components are stated using the
    bundled-structure API: `UnreducedAngles n`, `θ.activeSet`, `θ.product.apply`,
    `Vertex n`, and `S.digraph`. -/

/-- **Math.** The three classification theorems packaged as one triple. Adds no
mathematical content beyond `completeness`, `digraph_model`, and `rigid`
— this declaration exists so the project has a single Lean-side name to
cite the paper's Theorem 1. -/
theorem classification {n : ℕ} (hn : 2 ≤ n) :
    (∀ S : ActiveSet n, ∃ θ : UnreducedAngles n, θ.activeSet = S) ∧
    (∀ θ : UnreducedAngles n, θ.product.supportDigraph = θ.activeSet.digraph) ∧
    (∀ S S' : ActiveSet n,
      2 ≤ S.card → 2 ≤ S'.card →
      S.digraph ≅ S'.digraph → S = S') :=
  ⟨completeness, digraph_model hn, fun S S' => rigid S S' hn⟩

end HessenbergDigraphs
