/-
Copyright (c) 2026 Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Matrix.Givens.Rotation
import HessenbergDigraphs.Matrix.Givens.Product

/-!
# Examples and reusability tests for the Givens API

This file exists to validate the *reusability* of the
`HessenbergDigraphs.Matrix.Givens.{Rotation,Product}` modules in isolation: every
result here uses *only* the public API of the Givens / sign-equivalence /
Hessenberg modules and has no dependency on the Hessenberg-paper-specific
content (`Arc`, `activeSet`, `D_n(S)`, `ValidActiveSet`, …).

If a future change to the Givens API breaks one of these examples, that is
precisely the design signal we want: the public API has regressed in expressive
power for some non-Hessenberg use case.

## Examples

* `Matrix.givensRotation_two_form` — for `n = 2`, the four entries of
  `Matrix.givensRotation 2 ⟨0, _⟩ θ` are the textbook
  `[[cos θ, -sin θ], [sin θ, cos θ]]`.
* `Matrix.givensRotation_two_eq_matrix` — the same statement bundled into a
  single matrix-literal equation.
* `Matrix.givensRotation_two_orthogonal` — for `n = 2` the `Gᵀ G = 1`
  identity is the immediate concrete instance of the general lemma.
* `Matrix.givensProduct_one_eq_one` — for `n = 1`, `givensProduct` is the
  empty product, hence the identity.
-/

namespace Matrix

/-! ### Entry-level form for `n = 2` -/

/-! ## Mathematical layer — paper-side example: at `n = 2`, the four
    rotation-block entries are precisely `[[cos θ, -sin θ], [sin θ, cos θ]]`
    (Golub & Van Loan §5.1, the textbook 2×2 rotation). Each component is
    one of `EntryAccess.lean`'s four entry-level lemmas applied to the unique
    block index `k = ⟨0, _⟩ : Fin 1`. -/

/-- **Math.** For `n = 2`, the four entries of `givensRotation 2 ⟨0, _⟩ θ` are precisely
`[[cos θ, -sin θ], [sin θ, cos θ]]`. Each component is one of the four
entry-level lemmas applied to the unique block index `⟨0, _⟩ : Fin 1`. -/
theorem givensRotation_two_form (θ : ℝ) :
    let G : Matrix (Fin 2) (Fin 2) ℝ := givensRotation 2 ⟨0, by omega⟩ θ
    G 0 0 = Real.cos θ ∧ G 1 0 = Real.sin θ ∧
      G 0 1 = -Real.sin θ ∧ G 1 1 = Real.cos θ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact givensRotation.apply_self_self ⟨0, by omega⟩ θ
  · exact givensRotation.apply_succ_self ⟨0, by omega⟩ θ
  · exact givensRotation.apply_self_succ ⟨0, by omega⟩ θ
  · exact givensRotation.apply_succ_succ ⟨0, by omega⟩ θ

/-! ## Mathematical layer — same fact as `givensRotation_two_form`
    packaged as a single matrix-literal equation, via `ext + fin_cases` and
    the four entry-level lemmas. -/

/-- **Math.** Bundled matrix-literal form of `givensRotation_two_form`: the `2 × 2`
Givens rotation equals the textbook rotation matrix. -/
theorem givensRotation_two_eq_matrix (θ : ℝ) :
    (givensRotation 2 ⟨0, by omega⟩ θ : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact givensRotation.apply_self_self ⟨0, by omega⟩ θ
  · exact givensRotation.apply_self_succ ⟨0, by omega⟩ θ
  · exact givensRotation.apply_succ_self ⟨0, by omega⟩ θ
  · exact givensRotation.apply_succ_succ ⟨0, by omega⟩ θ

/-! ### Orthogonality at `n = 2` -/

/-! ## Mathematical layer — `Gᵀ G = 1` for the `n = 2` instance, by
    direct specialization of `givensRotation_orthogonal`. -/

/-- **Math.** For `n = 2`, `Gᵀ G = 1` is an immediate instance of the general
orthogonality lemma. -/
theorem givensRotation_two_orthogonal (θ : ℝ) :
    let G : Matrix (Fin 2) (Fin 2) ℝ := givensRotation 2 ⟨0, by omega⟩ θ
    Gᵀ * G = 1 :=
  givensRotation_orthogonal ⟨0, by omega⟩ θ

/-! ### Edge case: `n = 1` -/

/-! ## Mathematical layer — boundary case at `n = 1`: the canonical Givens
    product is over `Fin 0` (empty list), so its `List.prod` is the
    identity matrix. Tests the boundary handling of `givensProduct`. -/

/-- **Math.** For `n = 1`, `givensProduct` is the product over `Fin 0` and hence the
identity. The example tests the boundary handling of the product API. -/
theorem givensProduct_one_eq_one (θ : Fin 0 → ℝ) :
    (givensProduct θ : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
  unfold givensProduct
  simp

end Matrix
