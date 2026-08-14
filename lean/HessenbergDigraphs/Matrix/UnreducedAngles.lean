/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import HessenbergDigraphs.Vertex
import HessenbergDigraphs.ActiveSet
import HessenbergDigraphs.Matrix.OrthogonalHessenberg
import HessenbergDigraphs.Matrix.Givens.Product

/-!
# UnreducedAngles: paper-side unreduced angle vector

`UnreducedAngles n` is the paper-side bundle of the `n - 1` real
angles `θ_1, …, θ_{n-1}` together with the unreduced predicate
`∀ k, sin (θ_k) ≠ 0`. The legacy interface (`(θ : Fin (n - 1) → ℝ)
(hunred : ∀ k : Fin (n - 1), Real.sin (θ k) ≠ 0)`) is preserved via
the `toFinFunction` / `fromFinFunction` bridges.

The `angles` field is indexed by `Vertex (n - 1)` (paper-side
1-indexed) rather than `Fin (n - 1)` (Lean 0-indexed). The bridge to
`Matrix.givensProduct` (which takes `Fin (n - 1) → ℝ`) is performed
once in `toFinFunction` / `product`.

## Boundary cases

For `n ∈ {0, 1}`, `Vertex (n - 1) = Vertex 0` is empty (no value
satisfies `1 ≤ value ≤ 0`), so `Vertex 0 → ℝ` is the unique vacuous
function and `is_unreduced : ∀ k : Vertex 0, …` is vacuously true.
Thus `UnreducedAngles 0` and `UnreducedAngles 1` each have a unique
inhabitant. The derived `activeSet` is empty in those cases; the
derived `product` is the unique 0×0 matrix (`n = 0`) or the 1×1
identity (`n = 1`). This matches the legacy `Fin (n - 1) → ℝ`
behaviour (`Fin 0 → ℝ` is also vacuously unique for `n ∈ {0, 1}`).

## Main definitions

* `UnreducedAngles n` — structure with `angles : Vertex (n - 1) → ℝ`
  and `is_unreduced : ∀ k, sin (angles k) ≠ 0`.
* `UnreducedAngles.toFinFunction` / `fromFinFunction` — bridges to
  the legacy `Fin (n - 1) → ℝ` interface.
* `UnreducedAngles.activeSet` — paper-side `S = {k : cos θ_k ≠ 0}`
  as an `ActiveSet n`.
* `UnreducedAngles.product` — the canonical Givens product as an
  `OrthogonalHessenberg n`.

## References

Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" — §2
(Givens factorization parameters); Golub & Van Loan §5.1.
-/

namespace HessenbergDigraphs

open Matrix

/-! ## Mathematical layer — paper-side bundle: an unreduced angle vector
    is `n - 1` real angles indexed by `Vertex (n - 1)` (paper 1-indexed),
    together with the unreduced predicate. Boundary cases `n ∈ {0, 1}`
    yield the unique trivial inhabitant via the vacuous function on
    `Vertex 0`. -/

/-- **Math.** A paper-side unreduced angle vector: `n - 1` real angles indexed by
`Vertex (n - 1)`, together with the unreduced condition that every sine
is non-zero. -/
@[ext]
structure UnreducedAngles (n : ℕ) where
  angles : Vertex (n - 1) → ℝ
  is_unreduced : ∀ k, Real.sin (angles k) ≠ 0

namespace UnreducedAngles

variable {n : ℕ}

/-! ### Bridges to the legacy `Fin (n - 1) → ℝ` interface -/

/-! ## Engineering layer — Type B bridges to legacy `Fin (n - 1) → ℝ`
    callers (which are the matrix-side `Matrix.givensProduct` etc.).
    `toFinFunction` shifts the paper-side `Vertex (n - 1)` index down by
    one to match `Fin (n - 1)`; `fromFinFunction` does the inverse. -/

/-- **Eng.** Convert to the legacy `Fin (n - 1) → ℝ` form: `f k = angles ⟨k.val + 1, …⟩`. -/
def toFinFunction (θ : UnreducedAngles n) : Fin (n - 1) → ℝ :=
  fun k => θ.angles
    { value := k.val + 1
      one_le_value := Nat.succ_le_succ (Nat.zero_le _)
      value_le_n := by have := k.isLt; omega }

/-- **Eng.** Build an `UnreducedAngles n` from a legacy `Fin (n - 1) → ℝ` plus the
unreduced predicate. -/
def fromFinFunction (f : Fin (n - 1) → ℝ) (h : ∀ k, Real.sin (f k) ≠ 0) :
    UnreducedAngles n where
  angles := fun v =>
    f ⟨v.value - 1, by have := v.value_le_n; have := v.one_le_value; omega⟩
  is_unreduced := fun v =>
    h ⟨v.value - 1, by have := v.value_le_n; have := v.one_le_value; omega⟩

/-! ### Paper-side derived: `activeSet` -/

/-! ## Mathematical layer — Paper §3 / Bridge: `S(θ) = {k ∈ [n-1] :
    cos(θ_k) ≠ 0}`. Built by enumerating `Fin (n - 1)`, filtering by
    `cos ≠ 0`, then mapping each surviving `Fin` index to its
    `Vertex (n - 1)` counterpart (`+ 1` shift). Noncomputable because
    `Real.cos` is. -/

/-- **Math.** The paper-side active set `S(θ) = {k ∈ [n - 1] : cos(θ_k) ≠ 0}`. -/
noncomputable def activeSet (θ : UnreducedAngles n) : ActiveSet n where
  elements :=
    ((Finset.univ : Finset (Fin (n - 1))).filter
       (fun k => Real.cos (θ.toFinFunction k) ≠ 0)).image
      (fun k =>
        ({ value := k.val + 1
           one_le_value := Nat.succ_le_succ (Nat.zero_le _)
           value_le_n := by have := k.isLt; omega } : Vertex (n - 1)))

/-! ### Paper-side derived: `product` (the canonical Givens product) -/

/-! ## Mathematical layer — Paper §2 / Golub–Van Loan §5.1: the canonical
    Givens product of the angles, packaged as an `OrthogonalHessenberg n`.
    The orthogonality and Hessenberg proofs are pulled directly from
    `Matrix.Givens.Product`. -/

/-- **Math.** The canonical Givens product as an `OrthogonalHessenberg n`. -/
noncomputable def product (θ : UnreducedAngles n) : OrthogonalHessenberg n where
  matrix := Matrix.givensProduct θ.toFinFunction
  orthogonal := Matrix.givensProduct_isOrthogonal _
  hessenberg := Matrix.givensProduct_isUpperHessenberg _

/-- **Math.** The canonical Givens product of `θ` is unreduced: every spine entry
`(j + 1, j)` of `θ.product` equals `sin (θ_j) ≠ 0`
(`Matrix.givensProduct_apply_subdiag_eq_sin` and `θ.is_unreduced`). -/
theorem product_isUnreduced (θ : UnreducedAngles n) : θ.product.IsUnreduced := by
  intro j hj
  have hk1 : (j.toFin : ℕ) + 1 < n := by
    have := j.one_le_value
    change j.value - 1 + 1 < n
    omega
  have hnext : (j.next hj).toFin = (⟨(j.toFin : ℕ) + 1, hk1⟩ : Fin n) := by
    apply Fin.ext
    change j.value + 1 - 1 = j.value - 1 + 1
    have := j.one_le_value
    omega
  change Matrix.givensProduct θ.toFinFunction (j.next hj).toFin j.toFin ≠ 0
  rw [hnext, Matrix.givensProduct_apply_subdiag_eq_sin θ.toFinFunction j.toFin hk1]
  exact θ.is_unreduced _

/-! ## Mixed — Math: `fromFinFunction` followed by `toFinFunction`
    recovers the original `Fin (n - 1) → ℝ` function (round-trip on
    the legacy bridge). | Eng: by `funext` + `Vertex.toFin / ofFin`
    arithmetic. -/

/-- **Mixed.** Round-trip through the legacy bridge: `toFinFunction ∘ fromFinFunction = id`. -/
theorem toFinFunction_fromFinFunction (f : Fin (n - 1) → ℝ)
    (h : ∀ k, Real.sin (f k) ≠ 0) :
    (fromFinFunction f h).toFinFunction = f := by
  funext k
  change f ⟨k.val + 1 - 1, _⟩ = f k
  congr 1

end UnreducedAngles

end HessenbergDigraphs
