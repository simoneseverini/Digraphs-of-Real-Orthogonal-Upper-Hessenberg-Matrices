/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import Mathlib.Order.RelIso.Basic
import HessenbergDigraphs.Vertex

/-!
# Digraph: binary arc relations on `Vertex n`

A `Digraph n` is a binary relation on `Vertex n` — exactly what the paper
calls "a directed graph on the vertex set `[n] = {1, …, n}`". Encoded
as the abbrev `Vertex n → Vertex n → Prop` so that `D i j` directly
expresses "there is an arc from `i` to `j`" with zero wrapper overhead.

This file introduces the `Digraph n` abbrev, its isomorphism predicate
`isIsomorphicTo` (defined as `Nonempty (D ≃r D')` over Mathlib's
`RelIso`), and the paper-aligned scoped notation `D ≅ D'`.

## Main definitions

* `Digraph n` — abbrev for `Vertex n → Vertex n → Prop`.
* `Digraph.isIsomorphicTo` — `Nonempty (D ≃r D')`. Paper's `D ≅ D'`.
* Scoped notation `D ≅ D'` for `Digraph.isIsomorphicTo D D'`.

## Implementation notes

* `Digraph` is an `abbrev`, not a `structure`: a digraph is *exactly*
  a binary relation, so any wrapping adds no semantic content. All
  Mathlib relation-algebra API applies directly.
* The isomorphism `Type` form is Mathlib's `D ≃r D'` (`RelIso D D'`,
  built from an `Equiv.Perm (Vertex n)` plus a relation-preservation
  proof). It carries the bijection as data.
* The isomorphism `Prop` form is `D ≅ D'`, defined as
  `Nonempty (D ≃r D')` — the existential statement that some iso
  exists, matching paper's `D ≅ D'`.
* Adopting Mathlib `RelIso` gives us free access to `RelIso.refl`,
  `.symm`, `.trans`, plus the `FunLike` / `RelHomClass` ecosystem.

## References

Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" — §0
(directed graphs on `[n]`).
-/

namespace HessenbergDigraphs

/-! ## Mathematical layer — paper-side definition: a digraph on `[n]` is
    a binary arc relation on `Vertex n`. The `abbrev` form means `D i j`
    directly states "`i → j` is an arc". -/

/-- **Math.** A directed graph on `Vertex n`: a binary arc relation. -/
abbrev Digraph (n : ℕ) := Vertex n → Vertex n → Prop

namespace Digraph

variable {n : ℕ}

/-! ## Mathematical layer — paper's `D ≅ D'`: the existential that some
    relation isomorphism (`Mathlib.RelIso`) carries `D` to `D'`. The
    constructive `Type` form is `D ≃r D'`; the proposition form
    `Nonempty (D ≃r D')` matches paper's `≅`. -/

/-- **Math.** `D` and `D'` are isomorphic: there exists a Mathlib `RelIso` between
them. The constructive form `D ≃r D'` carries the bijection as data;
this `Nonempty` form is the existential matching paper's `D ≅ D'`. -/
abbrev isIsomorphicTo (D D' : Digraph n) : Prop := Nonempty (D ≃r D')

/-- **Eng.** Paper-side scoped notation: `D ≅ D'` unfolds to
`Digraph.isIsomorphicTo D D'`. Scoped to avoid clashing with
`CategoryTheory.Iso.≅`. -/
scoped infix:50 " ≅ " => Digraph.isIsomorphicTo

/-! ## Mathematical layer — demonstration: every digraph is isomorphic
    to itself, via Mathlib's `RelIso.refl`. -/

/-- **Math.** `≅` is reflexive, via Mathlib `RelIso.refl`. -/
theorem isIsomorphicTo_refl (D : Digraph n) : D ≅ D := ⟨RelIso.refl D⟩

end Digraph

end HessenbergDigraphs
