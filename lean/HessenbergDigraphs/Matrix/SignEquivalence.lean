/-
Copyright (c) 2026 Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Simone Severini
-/
import Util.Linter.MathTag
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.SplitIfs
import HessenbergDigraphs.Matrix.SupportDigraph

/-!
# Sign equivalence of matrices

Two square matrices `Q, Q'` are *sign-equivalent* when `Q' = D_L · Q · D_R` for
some pair of `±1`-diagonal matrices `D_L, D_R`. This is the matrix-side
equivalence relation that the support pattern (zero/non-zero structure) of a
matrix is invariant under, and is the natural "canonical form up to signs"
relation for orthogonal Hessenberg matrices factored as Givens products
(`HessenbergDigraphs.Matrix.Givens.Factorization`).

## Main definitions

* `Matrix.SignEquiv Q Q'` — `Q' = D_L · Q · D_R` for some `±1`-diagonals
  `D_L, D_R`.

## Main results

* `Matrix.SignEquiv.refl`, `Matrix.SignEquiv.symm`, `Matrix.SignEquiv.trans` —
  the relation is reflexive, symmetric, and transitive.
* `Matrix.SignEquiv.preserves_support` — sign-equivalent matrices have
  identical zero/non-zero patterns.

## Implementation notes

The definition unpacks a pair of functions `dL, dR : Fin n → ℝ` together with
sign hypotheses, rather than an existential over diagonal matrices, to keep the
side-condition `dL i ∈ {1, -1}` directly available in proofs. The dot-notation
API `Matrix.SignEquiv.{refl,symm,trans,preserves_support}` is the intended
public surface.

`Matrix.SignEquiv.trans` exists because the universality theorem for orthogonal
Hessenberg matrices (`HessenbergDigraphs.Matrix.Givens.Factorization`,
forthcoming) accumulates sign equivalences across an inductive peel-off
argument and would otherwise have to chain `refl`/`symm` manually.

## References

Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" — Lemma 1.
-/

namespace Matrix

open Matrix Finset

/-! ## Mathematical layer — a *signature matrix* is a diagonal matrix whose
    diagonal entries are all `±1`. `IsSignatureMatrix` carries the witnessing
    diagonal vector, so the `±1` side-condition is recoverable in proofs by
    destructuring `⟨d, hd, rfl⟩`. -/

/-- **Math.** A *signature matrix*: a diagonal matrix whose diagonal entries are
all `±1`, i.e. `D = diagonal d` for some `d : Fin n → ℝ` with each `d i ∈ {1, -1}`. -/
def IsSignatureMatrix {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ d : Fin n → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧ D = diagonal d

/-! ## Mathematical layer — paper-side definition (Severini Lemma 1):
    `Q' = D_L · Q · D_R` for signature matrices `D_L, D_R`. -/

/-- **Math.** Two `n × n` matrices `Q` and `Q'` are sign-equivalent if `Q' = D_L · Q · D_R`
for some signature matrices `D_L, D_R`. -/
def SignEquiv {n : ℕ} (Q Q' : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ D_L D_R : Matrix (Fin n) (Fin n) ℝ,
    IsSignatureMatrix D_L ∧ IsSignatureMatrix D_R ∧ Q' = D_L * Q * D_R

/-! ## Engineering layer — Type C tool: a `±1`-valued diagonal squares to
    the identity matrix. Used twice in `SignEquiv.symm` (once for `dL`,
    once for `dR`) to invert the sign-equivalence equation. -/

/-- **Eng.** A diagonal whose entries are all `±1` squares to the identity matrix:
`diagonal d · diagonal d = 1` whenever `∀ i, d i = 1 ∨ d i = -1`. -/
private lemma diagonal_mul_self_eq_one_of_isPlusMinusOne {n : ℕ}
    (d : Fin n → ℝ) (hd : ∀ i, d i = 1 ∨ d i = -1) :
    diagonal d * diagonal d = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h; rcases hd i with h | h <;> simp [h]
  · rfl

namespace SignEquiv

variable {n : ℕ}

/-! ## Mathematical layer — reflexivity of `SignEquiv` via the all-ones
    diagonals: every `Q = 1 · Q · 1` (`diagonal_one`). -/

/-- **Math.** Sign equivalence is reflexive. -/
theorem refl (Q : Matrix (Fin n) (Fin n) ℝ) : SignEquiv Q Q :=
  ⟨diagonal 1, diagonal 1, ⟨1, fun _ => Or.inl rfl, rfl⟩, ⟨1, fun _ => Or.inl rfl, rfl⟩,
    by simp⟩

/-! ## Mathematical layer — symmetry of `SignEquiv`: `±1`-diagonals are
    self-inverse (via `diagonal_mul_self_eq_one_of_isPlusMinusOne`), so
    left-multiplying both sides of `Q' = D_L · Q · D_R` by `D_L` (and right
    by `D_R`) recovers `Q`. -/

/-- **Math.** Sign equivalence is symmetric. -/
theorem symm {Q Q' : Matrix (Fin n) (Fin n) ℝ} (h : SignEquiv Q Q') :
    SignEquiv Q' Q := by
  obtain ⟨D_L, D_R, ⟨dL, hdL, rfl⟩, ⟨dR, hdR, rfl⟩, heq⟩ := h
  have hLinv := diagonal_mul_self_eq_one_of_isPlusMinusOne dL hdL
  have hRinv := diagonal_mul_self_eq_one_of_isPlusMinusOne dR hdR
  refine ⟨diagonal dL, diagonal dR, ⟨dL, hdL, rfl⟩, ⟨dR, hdR, rfl⟩, ?_⟩
  calc Q = 1 * Q * 1 := by simp
    _ = (diagonal dL * diagonal dL) * Q * (diagonal dR * diagonal dR) := by
        rw [hLinv, hRinv]
    _ = diagonal dL * (diagonal dL * Q * diagonal dR) * diagonal dR := by
        simp only [Matrix.mul_assoc]
    _ = diagonal dL * Q' * diagonal dR := by rw [← heq]

/-! ## Mathematical layer — transitivity of `SignEquiv`: compose two pairs
    of `±1`-diagonals into the pointwise products `i ↦ dL₂ i * dL₁ i` and
    `j ↦ dR₁ j * dR₂ j`, both still `±1`-valued. The equation collapses
    via `Matrix.diagonal_mul_diagonal`. Used by the universality theorem to
    accumulate sign equivalences along the inductive Givens factorization. -/

/-- **Math.** Sign equivalence is transitive. Used by the universality theorem
(`Matrix.exists_givensFactorization`) to accumulate sign equivalences along an
inductive argument. -/
theorem trans {Q₁ Q₂ Q₃ : Matrix (Fin n) (Fin n) ℝ}
    (h₁₂ : SignEquiv Q₁ Q₂) (h₂₃ : SignEquiv Q₂ Q₃) : SignEquiv Q₁ Q₃ := by
  obtain ⟨_, _, ⟨dL₁, hdL₁, rfl⟩, ⟨dR₁, hdR₁, rfl⟩, heq₁⟩ := h₁₂
  obtain ⟨_, _, ⟨dL₂, hdL₂, rfl⟩, ⟨dR₂, hdR₂, rfl⟩, heq₂⟩ := h₂₃
  refine ⟨diagonal (fun i => dL₂ i * dL₁ i), diagonal (fun j => dR₁ j * dR₂ j),
    ⟨fun i => dL₂ i * dL₁ i, ?_, rfl⟩, ⟨fun j => dR₁ j * dR₂ j, ?_, rfl⟩, ?_⟩
  · intro i
    rcases hdL₂ i with h₂ | h₂ <;> rcases hdL₁ i with h₁ | h₁ <;>
      simp [h₁, h₂]
  · intro j
    rcases hdR₁ j with h₁ | h₁ <;> rcases hdR₂ j with h₂ | h₂ <;>
      simp [h₁, h₂]
  · rw [heq₂, heq₁]
    rw [show (diagonal (fun i => dL₂ i * dL₁ i) : Matrix (Fin n) (Fin n) ℝ) =
        diagonal dL₂ * diagonal dL₁ from (Matrix.diagonal_mul_diagonal dL₂ dL₁).symm,
      show (diagonal (fun j => dR₁ j * dR₂ j) : Matrix (Fin n) (Fin n) ℝ) =
        diagonal dR₁ * diagonal dR₂ from (Matrix.diagonal_mul_diagonal dR₁ dR₂).symm]
    simp only [Matrix.mul_assoc]

/-! ## Mixed — Math: support invariance under sign equivalence — both sides'
    `(i, j)` entries are scalar multiples of each other by the non-zero
    `dL i * dR j`, so vanishing is preserved. | Eng: collapsing the
    `(diagonal dL * Q * diagonal dR) i j` matrix-product expansion to the
    closed-form `dL i * Q i j * dR j` via two nested `Finset.sum_eq_single`. -/

/-- **Math.** Sign-equivalent matrices have the same support: an entry is zero on one
side iff it is zero on the other. -/
theorem preserves_support {Q Q' : Matrix (Fin n) (Fin n) ℝ}
    (h : SignEquiv Q Q') (i j : Fin n) : Q i j ≠ 0 ↔ Q' i j ≠ 0 := by
  obtain ⟨D_L, D_R, ⟨dL, hdL, rfl⟩, ⟨dR, hdR, rfl⟩, heq⟩ := h
  have hdLne : ∀ i, dL i ≠ 0 := fun i => by rcases hdL i with h | h <;> simp [h]
  have hdRne : ∀ j, dR j ≠ 0 := fun j => by rcases hdR j with h | h <;> simp [h]
  have key : ∀ i j, Q' i j = dL i * Q i j * dR j := by
    intros i j; subst heq
    simp only [Matrix.mul_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single i]
      · simp
      · intros b _ hb; simp [show i ≠ b from Ne.symm hb]
      · simp
    · intros b _ hb; simp [hb]
    · simp
  constructor
  · intro hne; rw [key]; exact mul_ne_zero (mul_ne_zero (hdLne i) hne) (hdRne j)
  · intro hne; by_contra hq; rw [key, hq, mul_zero, zero_mul] at hne; exact hne rfl

end SignEquiv

/-! ## Mathematical layer — sign-invariance of the support digraph: since
    sign-equivalence preserves the zero / non-zero pattern
    (`SignEquiv.preserves_support`), the two support digraphs coincide. -/

/-- **Math.** Sign-equivalent matrices have the same support digraph:
`D(Q) = D(Q')` whenever `Q ≃sign Q'`. -/
theorem supportDigraph_eq_of_signEquiv {n : ℕ} {Q Q' : Matrix (Fin n) (Fin n) ℝ}
    (h : SignEquiv Q Q') : Q.supportDigraph = Q'.supportDigraph := by
  funext i j
  exact propext (SignEquiv.preserves_support h i j)

/-! ## Engineering layer — paper-side notation: `Q ≃sign Q'` for sign
    equivalence. Plain `infix` (not scoped) since `≃sign` is unique
    enough not to clash with other Mathlib equivalence symbols. -/

/-- **Eng.** Paper-side notation for sign equivalence: `Q ≃sign Q'` unfolds to
`Matrix.SignEquiv Q Q'`. -/
infix:50 " ≃sign " => Matrix.SignEquiv

end Matrix
