/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Realization.DigraphModel
import HessenbergDigraphs.Matrix.Givens.Factorization
import HessenbergDigraphs.Combinatorial.ClassCount
import HessenbergDigraphs.Compute.Query

/-!
# The calculator's class count certifies the matrix-realizable support count

This file is the bridge that makes the apex `classification` theorem
load-bearing for the executable calculator. On its own, the calculator's
output `countClasses n` (run by the `#hessenberg_count` command) is only
certified against the *combinatorial* object `D_n(S)`. Here it is connected
to the *matrix* side: the support digraphs realizable by unreduced Givens
products are exactly the combinatorial models `D_n(S)`, and up to isomorphism
they number `countClasses n`.

The proof routes through all three components of `classification`:

* `digraph_model` and `completeness` identify the realizable supports with
  `{ D_n(S) : S : ActiveSet n }` (`realizableSupports_eq_range`);
* `rigid` — via `card_isoClasses_quot` / `isoInvariant_eq_iff`, the same
  route as `countClasses_eq_isoQuot` — certifies the iso-class count.

## Main results

* `realizableSupports_eq_range` — the realizable support digraphs are exactly
  `{ D_n(S) : S }` (the matrix-side content of `classification`).
* `realizable_classCount` — packaged certificate tying the executable
  `countClasses n` to the matrix-realizable support count.

## References

Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" —
Theorem 1, Theorem 12.
-/

namespace HessenbergDigraphs

variable {n : ℕ}

/-- **Math.** The support digraphs realizable by unreduced Givens products:
those `D : Digraph n` arising as `θ.product.supportDigraph` for some
`θ : UnreducedAngles n`. -/
def realizableSupports (n : ℕ) : Set (Digraph n) :=
  { D | ∃ θ : UnreducedAngles n, θ.product.supportDigraph = D }

/-- **Math.** The realizable support digraphs are exactly the combinatorial
models `D_n(S)`: `realizableSupports n = { S.digraph : S : ActiveSet n }`. The
forward inclusion is `digraph_model` (every Givens-product support is some
`θ.activeSet.digraph`); the backward inclusion is `completeness` followed by
`digraph_model` (every `S` is realized by some `θ`). This is the matrix-side
content of `classification`. -/
theorem realizableSupports_eq_range (hn : 2 ≤ n) :
    realizableSupports n = Set.range (fun S : ActiveSet n => S.digraph) := by
  ext D
  simp only [realizableSupports, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨θ, rfl⟩
    exact ⟨θ.activeSet, (digraph_model hn θ).symm⟩
  · rintro ⟨S, rfl⟩
    obtain ⟨θ, hθ⟩ := completeness S
    exact ⟨θ, by rw [digraph_model hn θ, hθ]⟩

/-- **Math.** Certificate connecting the executable calculator to the matrix
side. Two facts together:

1. the support digraphs realizable by unreduced Givens products are exactly the
   combinatorial models `D_n(S)` (`digraph_model` + `completeness`);
2. up to isomorphism they number `countClasses n = 2 ^ (n - 1) - ⌊(n - 1) / 2⌋`,
   the cardinality of the quotient of active sets by support-digraph
   isomorphism (`card_isoClasses_quot`, backed by `rigid`).

Every component of `classification` is load-bearing here, so the calculator's
output is certified as a genuine count on the matrix side. Paper: Theorem 1 +
Theorem 12. -/
theorem realizable_classCount (hn : 2 ≤ n) :
    realizableSupports n = Set.range (fun S : ActiveSet n => S.digraph) ∧
      Nat.card (Quotient (isoSetoid n)) = countClasses n :=
  ⟨realizableSupports_eq_range hn, card_isoClasses_quot hn⟩

/-! ## Mathematical layer — strengthening to the genuine matrix class.

    The previous results speak of supports of canonical Givens products. We
    now lift them to the supports of *all* unreduced orthogonal upper
    Hessenberg matrices, using the universality theorem
    `OrthogonalHessenberg.exists_givensFactorization`, the support invariance of
    sign equivalence (`OrthogonalHessenberg.supportDigraph_eq_of_signEquivTo`),
    and the fact that every `θ.product` is unreduced (`product_isUnreduced`). -/

/-- **Math.** The support digraphs of *unreduced orthogonal upper Hessenberg
matrices*: those `D : Digraph n` arising as `Q.supportDigraph` for some
unreduced `Q : OrthogonalHessenberg n`. -/
def matrixRealizableSupports (n : ℕ) : Set (Digraph n) :=
  { D | ∃ Q : OrthogonalHessenberg n, Q.IsUnreduced ∧ Q.supportDigraph = D }

/-- **Math.** The support digraphs of unreduced orthogonal upper Hessenberg
matrices are *exactly* the combinatorial models `D_n(S)`. Forward: every such
matrix is sign-equivalent to some `θ.product`
(`OrthogonalHessenberg.exists_givensFactorization`), which has the same support
(`supportDigraph_eq_of_signEquivTo`), equal to `θ.activeSet.digraph`
(`digraph_model`). Backward: every `S` is realized by an unreduced `θ`
(`completeness`, `product_isUnreduced`) whose product has support `S.digraph`
(`digraph_model`). This is the full matrix-side content of `classification`
together with the universality theorem. -/
theorem matrixRealizableSupports_eq_range (hn : 2 ≤ n) :
    matrixRealizableSupports n = Set.range (fun S : ActiveSet n => S.digraph) := by
  ext D
  simp only [matrixRealizableSupports, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨Q, hu, rfl⟩
    obtain ⟨θ, hsign⟩ := OrthogonalHessenberg.exists_givensFactorization hn Q hu
    exact ⟨θ.activeSet, by
      rw [← digraph_model hn θ,
        ← OrthogonalHessenberg.supportDigraph_eq_of_signEquivTo hsign]⟩
  · rintro ⟨S, rfl⟩
    obtain ⟨θ, hθ⟩ := completeness S
    exact ⟨θ.product, θ.product_isUnreduced, by rw [digraph_model hn θ, hθ]⟩

/-- **Math.** The headline certificate: the support digraphs of unreduced
orthogonal upper Hessenberg `n × n` matrices are exactly the combinatorial
models `D_n(S)`, and up to isomorphism they number the executable calculator's
`countClasses n = 2 ^ (n - 1) - ⌊(n - 1) / 2⌋`. This routes through the entire
apex: universality (`exists_givensFactorization`) + sign-equivalence support
invariance, the bridge (`digraph_model`) + realizability (`completeness`), and
rigidity (`rigid`, via `card_isoClasses_quot`). It certifies that the number the
calculator prints is a genuine count on the matrix class itself. Paper:
Theorem 1 + Theorem 12. -/
theorem matrix_classCount (hn : 2 ≤ n) :
    matrixRealizableSupports n = Set.range (fun S : ActiveSet n => S.digraph) ∧
      Nat.card (Quotient (isoSetoid n)) = countClasses n :=
  ⟨matrixRealizableSupports_eq_range hn, card_isoClasses_quot hn⟩

end HessenbergDigraphs
