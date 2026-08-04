/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Vertex
import HessenbergDigraphs.ActiveSet
import HessenbergDigraphs.Combinatorial.Digraph

/-!
# Arc: inductive arc relation for `D_n(S)`

The combinatorial digraph model `D_n(S)` from
"Digraphs of Real Orthogonal Upper Hessenberg Matrices" by Severini.
This file provides the inductive `Arc` shape (spine + overlay
constructors) on top of the bundled `ActiveSet` / `Vertex` /
`Digraph` types, together with the `Loop` predicate.

The legacy ℕ-indexed `Arc`, the ℕ-side `activeRows` / `activeCols`
defs, the `ValidActiveSet` predicate, the `DigraphIso` def, and the
six Type-B engineering helpers all become unnecessary under the
bundled-structure API:

* Active-set bound `1 ≤ k ≤ n - 1` is carried by `Vertex (n - 1)`.
* `activeRows` / `activeCols` live on `ActiveSet n` (yielding
  `Finset (Vertex n)`), defined in `HessenbergDigraphs.ActiveSet`.
* `DigraphIso` becomes `S.digraph ≅ S'.digraph`.

## Main definitions

* `Arc S i j` — inductive arc relation with `spine` / `overlay`
  constructors. Equivalent to `S.digraph i j` (proven via
  `arc_iff_digraph`).
* `Loop S v` — `Arc S v v`.

## Implementation notes

* `Arc` is kept as an `inductive` (not as an alias for `S.digraph`) so
  downstream proofs can use `cases h with | spine | overlay` pattern
  matching with named constructors. The `arc_iff_digraph` bridge gives
  free conversion to/from `S.digraph` when needed.

## References

Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" — §0,
Theorem 7.
-/

namespace HessenbergDigraphs

variable {n : ℕ}

/-! ## Mathematical layer — Paper Theorem 7 (arc relation, inductive form). -/

/-- **Math.** Arc relation for `D_n(S)` (Paper: Theorem 7).

* `Arc.spine j h` — the spine arc `j.next h → j` for `h : j.value < n`.
* `Arc.overlay i j hi hj hij` — an overlay arc `i → j` whenever
  `i ∈ S.activeRows`, `j ∈ S.activeCols`, and `i ≤ j`. -/
inductive Arc (S : ActiveSet n) : Vertex n → Vertex n → Prop where
  | spine (j : Vertex n) (h : j.value < n) : Arc S (j.next h) j
  | overlay (i j : Vertex n) (hi : i ∈ S.activeRows) (hj : j ∈ S.activeCols)
      (hij : i ≤ j) : Arc S i j

/-! ## Mathematical layer — disjunctive view of `Arc`. -/

/-- **Math.** `Arc S i j` iff: spine-shape `(∃ h, i = j.next h)` or overlay shape. -/
theorem arc_iff_spine_or_overlay (S : ActiveSet n) (i j : Vertex n) :
    Arc S i j ↔
      (∃ h : j.value < n, i = j.next h) ∨
      (i ∈ S.activeRows ∧ j ∈ S.activeCols ∧ i ≤ j) := by
  constructor
  · intro h
    cases h with
    | spine k h => exact Or.inl ⟨h, rfl⟩
    | overlay _ _ hi hj hij => exact Or.inr ⟨hi, hj, hij⟩
  · rintro (⟨h, rfl⟩ | ⟨hi, hj, hij⟩)
    · exact Arc.spine _ h
    · exact Arc.overlay _ _ hi hj hij

/-! ## Mathematical layer — `Arc` and `S.digraph` agree. -/

/-- **Math.** `Arc S i j ↔ S.digraph i j`. -/
theorem arc_iff_digraph (S : ActiveSet n) (i j : Vertex n) :
    Arc S i j ↔ S.digraph i j := arc_iff_spine_or_overlay S i j

/-! ## Engineering layer — Type A: Decidable instance. -/

/-- **Eng.** Decidability of the spine existential. -/
instance decSpine (j i : Vertex n) :
    Decidable (∃ h : j.value < n, i = j.next h) :=
  if hlt : j.value < n then
    if heq : i = j.next hlt then
      isTrue ⟨hlt, heq⟩
    else
      isFalse fun ⟨_, h⟩ => heq h
  else
    isFalse fun ⟨h, _⟩ => hlt h

/-- **Eng.** Arc decidability via the disjunctive iff. -/
instance (S : ActiveSet n) (i j : Vertex n) : Decidable (Arc S i j) :=
  decidable_of_iff _ (arc_iff_spine_or_overlay S i j).symm

/-! ## Mathematical layer — Loop predicate. -/

/-- **Math.** A loop at `v`: `Arc S v v`. -/
abbrev Loop (S : ActiveSet n) (v : Vertex n) : Prop := Arc S v v

/-- **Math.** Build a self-loop at `v` from row + column membership. -/
theorem loop_of_mem {S : ActiveSet n} {v : Vertex n}
    (hi : v ∈ S.activeRows) (hj : v ∈ S.activeCols) : Loop S v :=
  Arc.overlay v v hi hj (Nat.le_refl v.value)

end HessenbergDigraphs
