/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Mathlib.Data.Nat.Fib.Basic
import HessenbergDigraphs.Combinatorial.Degree
import HessenbergDigraphs.Combinatorial.ClassCount
import HessenbergDigraphs.Compute.Enumerate

/-!
# Computable property queries for `D_n(S)`

Each query function returns a computed value; the accompanying theorem
ties it to the Prop-level result proved in the Combinatorial tier.

## Main definitions

* `ActiveSet.isLoopless` — `Bool` check, certified by `loopless_iff`.
* `ActiveSet.degreeList` — per-vertex `(outDeg, inDeg)` list.
* `countClasses` — number of isomorphism classes, by `count_formula`.
-/

namespace HessenbergDigraphs

variable {n : ℕ}

/-- **Eng.** Is `D_n(S)` loopless? -/
def ActiveSet.isLoopless (S : ActiveSet n) : Bool :=
  S.loopVertices.isEmpty

/-- **Eng.** Per-vertex `(vertex_value, outDeg, inDeg)`, ordered by vertex. -/
def ActiveSet.degreeList (S : ActiveSet n) :
    List (ℕ × ℕ × ℕ) :=
  ((List.finRange n).map Vertex.ofFin).map
    (fun v => (v.value, outDeg S v, inDeg S v))

/-- **Eng.** Number of connected isomorphism classes of `D_n(S)` for
given `n`, computed as `2^(n-1) - (n-1) / 2`. Backed by `count_formula`. -/
def countClasses (n : ℕ) : ℕ := 2 ^ (n - 1) - (n - 1) / 2

/-- **Eng.** Number of loopless connected isomorphism classes for given `n`,
computed as `Nat.fib (n - 1) - (n - 3) / 2`. Backed by
`count_loopless_formula`. -/
def countLooplessClasses (n : ℕ) : ℕ :=
  if n < 3 then 0 else Nat.fib (n - 1) - (n - 3) / 2

/-! ## Mathematical layer — specification of the property queries. The
    `Bool`/`List` outputs displayed by the calculator are characterised by
    the formal `Arc` relation and the formal `outDeg`/`inDeg`. -/

/-- **Math.** `degreeList` lists exactly the formal degrees: `(a, od, id)`
occurs iff `a = v.value`, `od = outDeg S v`, `id = inDeg S v` for some vertex
`v` of `D_n(S)`. -/
theorem mem_degreeList_iff (S : ActiveSet n) (a od id : ℕ) :
    (a, od, id) ∈ S.degreeList ↔
      ∃ v : Vertex n, v.value = a ∧ outDeg S v = od ∧ inDeg S v = id := by
  simp only [ActiveSet.degreeList, List.map_map, List.mem_map, Function.comp_apply,
    Prod.mk.injEq]
  constructor
  · rintro ⟨k, _, hk⟩
    exact ⟨Vertex.ofFin k, hk.1, hk.2.1, hk.2.2⟩
  · rintro ⟨v, rfl, rfl, rfl⟩
    exact ⟨v.toFin, List.mem_finRange _, by simp [Vertex.ofFin_toFin]⟩

/-- **Math.** `isLoopless` decides exactly the formal loopless property:
`S.isLoopless = true` iff `D_n(S)` carries no self-loop `Arc S v v`. Together
with `loopless_iff` this certifies the calculator's loopless verdict. -/
theorem isLoopless_iff (S : ActiveSet n) :
    S.isLoopless = true ↔ ∀ v : Vertex n, ¬ Arc S v v := by
  unfold ActiveSet.isLoopless
  rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h v harc
    exact h v.value ((mem_loopVertices_iff S v.value).mpr ⟨v, rfl, harc⟩)
  · intro h a hmem
    obtain ⟨v, _, harc⟩ := (mem_loopVertices_iff S a).mp hmem
    exact h v harc

/-- **Math.** Specification of the classification count: the calculator's output
`countClasses n` equals the number of isomorphism classes of `D_n(S)` — the
distinct values of the complete invariant `isoInvariant` (`card_isoClasses`,
with completeness `isoInvariant_eq_iff`). Paper: Theorem 12. -/
theorem countClasses_eq_card_isoClasses (hn : 2 ≤ n) :
    countClasses n = ((Finset.univ : Finset (ActiveSet n)).image isoInvariant).card :=
  (card_isoClasses hn).symm

/-- **Math.** Stronger specification of the classification count as a genuine
cardinality: the calculator's output `countClasses n` equals the number of
isomorphism classes of `D_n(S)`, i.e. the cardinality of the quotient of active
sets by support-digraph isomorphism (`isoSetoid`). Unlike
`countClasses_eq_card_isoClasses` — which only equates the count to the size of
`isoInvariant`'s image — this routes through `card_isoClasses_quot`, whose proof
uses the rigidity theorem `rigid` (via `isoInvariant_eq_iff`) to certify that
`isoInvariant` is a *complete* invariant. So this is the honest iso-class count.
Paper: Theorem 12. -/
theorem countClasses_eq_isoQuot (hn : 2 ≤ n) :
    countClasses n = Nat.card (Quotient (isoSetoid n)) :=
  (card_isoClasses_quot hn).symm

/-- **Math.** Specification of the loopless count: the calculator's output
`countLooplessClasses n` equals the number of loopless isomorphism classes of
`D_n(S)` (`card_looplessClasses`, with completeness `isoInvariant_eq_iff`).
Paper: Theorem 15. The `fib` lower bound `hfib` is the side condition of
`count_loopless_formula`. -/
theorem countLooplessClasses_eq_card_looplessClasses (hn : 3 ≤ n)
    (hfib : n - 3 + 1 ≤ Nat.fib (n - 1)) :
    countLooplessClasses n
      = ((Finset.univ.filter (fun S : ActiveSet n => IsLooplessSet S)).image
          isoInvariant).card := by
  unfold countLooplessClasses
  rw [if_neg (by omega)]
  exact (card_looplessClasses hn hfib).symm

end HessenbergDigraphs
