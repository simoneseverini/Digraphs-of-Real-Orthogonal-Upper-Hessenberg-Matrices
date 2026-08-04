/-
Copyright (c) 2026 Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Simone Severini
-/
import Util.Linter.MathTag
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import HessenbergDigraphs.Matrix.Givens.Product
import HessenbergDigraphs.Matrix.SignEquivalence
import HessenbergDigraphs.Matrix.Orthogonal
import HessenbergDigraphs.Matrix.OrthogonalHessenberg
import HessenbergDigraphs.Matrix.UnreducedAngles

/-!
# Factorization-side results for the Givens product

This file collects results of "factorization shape" — facts that describe how
the canonical Givens product `Matrix.givensProduct` decomposes when one or
more of its sine angles vanish.

## Main results

* `Matrix.givensProduct_apply_of_break` — if `sin θ_k = 0`, then every
  upper-right entry of `givensProduct θ` whose row index is `≤ k` and column
  index is `≥ k + 1` vanishes. Equivalently, the product is block-diagonal
  with blocks straddling row `k` / column `k + 1`.
* `Matrix.exists_givensFactorization` — universality:
  every orthogonal upper Hessenberg matrix is sign-equivalent to a
  `givensProduct θ` for some `θ`.

## References

Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" — §3.
-/

namespace Matrix

open Matrix Finset

variable {n : ℕ}

/-- **Math.** If `sin θ_k = 0`, then every entry of `givensProduct θ` straddling the
`k / (k + 1)` boundary vanishes; equivalently, the canonical Givens product is
block-diagonal at row `k` / column `k + 1`. -/
theorem givensProduct_apply_of_break (θ : Fin (n - 1) → ℝ)
    (k : Fin (n - 1)) (hbreak : Real.sin (θ k) = 0)
    (i j : Fin n) (hi : i.val ≤ k.val) (hj : j.val ≥ k.val + 1) :
    givensProduct θ i j = 0 := by
  unfold givensProduct
  suffices key : ∀ m (hm : m ≤ n - 1), m ≥ k.val + 1 →
      ∀ col : Fin n, col.val ≥ k.val + 1 →
      (List.ofFn fun t : Fin m =>
          givensRotation n ⟨t, by omega⟩ (θ ⟨t, by omega⟩)).prod
        i col = 0 by
    exact key (n - 1) le_rfl (by omega) j hj
  intro m
  induction m with
  | zero => intro _ hge; omega
  | succ m ih =>
    intro hm hge col hcol
    rw [partialGivensProduct_succ_eq θ m hm, Matrix.mul_apply]
    apply Finset.sum_eq_zero; intro x _
    by_cases hmeq : m = k.val
    · by_cases hx : x.val ≥ k.val + 1
      · rw [partialGivensProduct_apply_of_col_ge θ m (by omega) x (by omega) i]
        simp [Fin.ext_iff]; omega
      · push_neg at hx
        suffices hGzero : givensRotation n ⟨m, by omega⟩ (θ ⟨m, by omega⟩) x col = 0 by
          rw [hGzero, mul_zero]
        by_cases hcolk1 : col.val = k.val + 1
        · have hcol_eq : col = ⟨k.val + 1, by omega⟩ := Fin.ext (by omega)
          rw [hcol_eq]; subst hmeq
          unfold givensRotation
          simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
          have hx_ne_k1 : x ≠ (⟨k.val + 1, by omega⟩ : Fin n) := by
            intro h; simp [Fin.ext_iff] at h; omega
          by_cases hxk : x = ⟨k.val, by omega⟩
          · simp [hxk, hbreak]
          · simp [hx_ne_k1, Ne.symm hxk, Ne.symm hx_ne_k1]
        · have : col.val ≠ k.val := by omega
          have : col.val ≠ k.val + 1 := hcolk1
          subst hmeq
          rw [givensRotation.apply_of_ne_col ⟨k.val, by omega⟩ _ x col
              (by simp; omega) (by simp; omega)]
          simp; omega
    · have hmge : m ≥ k.val + 1 := by omega
      by_cases hx : x.val ≥ k.val + 1
      · rw [ih (by omega) hmge x hx, zero_mul]
      · push_neg at hx
        have hGid : givensRotation n ⟨m, by omega⟩ (θ ⟨m, by omega⟩) x col =
            if x = col then 1 else 0 :=
          givensRotation.apply_of_ne_row ⟨m, by omega⟩ _ x col (by simp; omega) (by simp; omega)
        rw [hGid]
        simp [show x ≠ col by intro h; subst h; omega]

/-! ### Universality of the canonical Givens factorization

The theorem `exists_givensFactorization` is the converse direction to
`givensProduct_isUpperHessenberg`: given an orthogonal upper Hessenberg `Q`,
peel off Givens rotations until `Q` is reduced to the identity, then reassemble.

The reduction step uses these private sublemmas:
* `last_row_norm` — the last row's two non-zero entries have unit-norm sum-of-squares.
* `exists_angle_for_last_row` — given `(a, b)` with `a² + b² = 1`, find `θ` with
  `cos θ = b`, `sin θ = a`.
* `mul_givens_last_clears` — right-multiplying by the right Givens rotation
  forces the last row of `Q · Gᵀ` to be `e_{n-1}ᵀ`.
* `last_col_eq_e_n_of_orthogonal` — orthogonality + last-row-canonical forces
  the last column to be `e_{n-1}`.
* `mul_givens_transpose_isUpperHessenberg` — Hessenberg is preserved under
  right-multiplication by the transpose of the rightmost Givens factor.
* `block_decomposition` — the principal `(n-1) × (n-1)` corner of `Q · Gᵀ`
  is itself orthogonal upper Hessenberg. -/

/-- **Math.** For an orthogonal upper Hessenberg `n × n` matrix (`n ≥ 2`), the
sum of squares `Q[n-1, n-2]² + Q[n-1, n-1]²` equals `1`. The Hessenberg
hypothesis forces all earlier columns of the last row to vanish, leaving
just these two entries to absorb the unit norm imposed by `Q Qᵀ = 1`. -/
private theorem last_row_norm (hn : 2 ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℝ)
    (hortho : Q.IsOrthogonal) (hhess : Q.IsUpperHessenberg) :
    Q ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩ ^ 2 +
      Q ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ ^ 2 = 1 := by
  -- Row n - 1 has unit ℓ²-norm because (Q Qᵀ)[n-1, n-1] = 1.
  have hQQt : Q * Qᵀ = 1 := hortho.mul_self_transpose
  have hrow : ∑ j : Fin n, Q ⟨n - 1, by omega⟩ j ^ 2 = 1 := by
    have h := congrArg (fun M : Matrix _ _ _ => M ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩) hQQt
    simp only [Matrix.one_apply_eq, Matrix.mul_apply, Matrix.transpose_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl (fun j _ => sq (Q _ j) ▸ rfl)
  -- The non-vanishing support of row n - 1 is the 2-element set {n - 2, n - 1}.
  set i : Fin n := ⟨n - 1, by omega⟩ with hi_def
  set p : Fin n := ⟨n - 2, by omega⟩ with hp_def
  have hpi : p ≠ i := fun h => by simp [p, i, Fin.ext_iff] at h; omega
  let supp : Finset (Fin n) := {p, i}
  have hvan : ∀ j : Fin n, j ∉ supp → Q i j ^ 2 = 0 := by
    intro j hj
    simp only [supp, Finset.mem_insert, Finset.mem_singleton] at hj
    push_neg at hj
    obtain ⟨hjp, hji⟩ := hj
    have hjval : j.val + 1 < n - 1 := by
      have := j.isLt
      have hp : j.val ≠ n - 2 := fun h => hjp (Fin.ext (by simp only [p]; exact h))
      have hi : j.val ≠ n - 1 := fun h => hji (Fin.ext (by simp only [i]; exact h))
      omega
    rw [hhess i j (by simp [i]; omega)]; ring
  have hsum_eq : ∑ j ∈ supp, Q i j ^ 2 = ∑ j : Fin n, Q i j ^ 2 :=
    Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => hvan j hj)
  rw [← hsum_eq] at hrow
  rw [show supp = insert p {i} from rfl, Finset.sum_insert (by simp [hpi]),
      Finset.sum_singleton] at hrow
  exact hrow

/-- **Math.** For any real pair `(a, b)` with `a² + b² = 1`, there exists an angle `θ`
with `cos θ = b` and `sin θ = a`. The construction uses `Real.arccos b`
(which gives `cos θ = b` and `sin θ = √(1 - b²) = |a|`) and flips the sign
when `a < 0`. -/
theorem exists_angle_for_last_row (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = b ∧ Real.sin θ = a := by
  have hb1 : -1 ≤ b := by nlinarith [sq_nonneg a]
  have hb2 : b ≤ 1 := by nlinarith [sq_nonneg a]
  by_cases ha : 0 ≤ a
  · refine ⟨Real.arccos b, Real.cos_arccos hb1 hb2, ?_⟩
    rw [Real.sin_arccos, show 1 - b ^ 2 = a ^ 2 from by linarith,
      Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
  · push_neg at ha
    refine ⟨-Real.arccos b, ?_, ?_⟩
    · rw [Real.cos_neg, Real.cos_arccos hb1 hb2]
    · rw [Real.sin_neg, Real.sin_arccos, show 1 - b ^ 2 = a ^ 2 from by linarith,
        Real.sqrt_sq_eq_abs, abs_of_neg ha]
      ring

/-- **Math.** Right-multiplying an orthogonal upper Hessenberg matrix `Q` by the
transpose of `givensRotation ⟨n-2, _⟩ θ`, with `cos θ = Q[n-1, n-1]` and
`sin θ = Q[n-1, n-2]`, produces a matrix whose last row is the standard basis
vector `e_{n-1}ᵀ`. -/
private theorem mul_givens_last_clears (hn : 2 ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℝ)
    (hortho : Q.IsOrthogonal) (hhess : Q.IsUpperHessenberg)
    (θ : ℝ)
    (hcos : Real.cos θ = Q ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩)
    (hsin : Real.sin θ = Q ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩) :
    ∀ j : Fin n,
      (Q * (givensRotation n ⟨n - 2, by omega⟩ θ)ᵀ) ⟨n - 1, by omega⟩ j =
        if j = ⟨n - 1, by omega⟩ then 1 else 0 := by
  intro j
  have hnorm := last_row_norm hn Q hortho hhess
  -- Abbreviations.
  set i : Fin n := ⟨n - 1, by omega⟩
  set p : Fin n := ⟨n - 2, by omega⟩
  set k : Fin (n - 1) := ⟨n - 2, by omega⟩
  set G : Matrix (Fin n) (Fin n) ℝ := givensRotation n k θ
  -- The two block-diagonal Fin-n indices coincide with k.val and k.val+1.
  have hp_eq : p = (⟨k.val, by simp [k]; omega⟩ : Fin n) := rfl
  have hi_eq : i = (⟨k.val + 1, by simp [k]; omega⟩ : Fin n) := by
    simp [i, k, Fin.ext_iff]; omega
  have hpi : p ≠ i := fun h => by simp [p, i, Fin.ext_iff] at h; omega
  -- Expand and reduce the matrix product to a 2-element sum.
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  have hsupp : ∀ x : Fin n, x ∉ ({p, i} : Finset (Fin n)) → Q i x * G j x = 0 := by
    intros x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    push_neg at hx
    have hxp : x.val ≠ n - 2 := fun h => hx.1 (Fin.ext (by simp only [p]; exact h))
    have hxi : x.val ≠ n - 1 := fun h => hx.2 (Fin.ext (by simp only [i]; exact h))
    have := x.isLt
    rw [hhess ⟨n - 1, by omega⟩ x (by simp; omega), zero_mul]
  rw [(Finset.sum_subset (Finset.subset_univ ({p, i} : Finset (Fin n)))
        (fun x _ hx => hsupp x hx)).symm]
  rw [show ({p, i} : Finset (Fin n)) = insert p {i} from rfl,
      Finset.sum_insert (by simp [hpi]), Finset.sum_singleton]
  -- Goal:  Q[i,p] * G[j,p] + Q[i,i] * G[j,i] = if j = i then 1 else 0
  -- Express G[j,p] and G[j,i] case-by-case on j.
  by_cases hjp : j.val = k.val
  · -- j sits in the block at row k = n-2. Then j = p, G[p,p] = cos θ, G[p,i] = -sin θ.
    have hj_eq_p : j = p := by simp only [hp_eq, Fin.ext_iff]; exact hjp
    have hj_ne_i : j ≠ i := by rw [hj_eq_p]; exact hpi
    rw [if_neg hj_ne_i]
    have hGjp : G j p = Real.cos θ := by
      rw [hj_eq_p, hp_eq]; exact givensRotation.apply_self_self k θ
    have hGji : G j i = -Real.sin θ := by
      rw [hj_eq_p, hi_eq]; exact givensRotation.apply_self_succ k θ
    rw [hGjp, hGji, hcos, hsin]
    ring
  by_cases hji_val : j.val = k.val + 1
  · -- j sits in the block at row k+1 = n-1. Then j = i, G[i,p] = sin θ, G[i,i] = cos θ.
    have hj_eq_i : j = i := by simp only [hi_eq, Fin.ext_iff]; exact hji_val
    rw [if_pos hj_eq_i]
    have hGjp : G j p = Real.sin θ := by
      rw [hj_eq_i, hi_eq, hp_eq]; exact givensRotation.apply_succ_self k θ
    have hGji : G j i = Real.cos θ := by
      rw [hj_eq_i, hi_eq]; exact givensRotation.apply_succ_succ k θ
    rw [hGjp, hGji, hcos, hsin]
    have hsq : Q i p ^ 2 + Q i i ^ 2 = 1 := by
      convert hnorm using 2
    nlinarith [hsq]
  · -- j outside the block: G[j, *] is the identity row; G[j, p] = G[j, i] = 0
    -- because j ≠ p (j.val ≠ k.val = n-2) and j ≠ i (j.val ≠ k.val + 1 = n-1).
    have hj_ne_p : j ≠ p := fun h => hjp (by rw [h, hp_eq])
    have hj_ne_i : j ≠ i := fun h => hji_val (by rw [h, hi_eq])
    rw [if_neg hj_ne_i]
    change Q i p * givensRotation n k θ j p + Q i i * givensRotation n k θ j i = 0
    rw [givensRotation.apply_of_ne_row k θ j p hjp hji_val,
        givensRotation.apply_of_ne_row k θ j i hjp hji_val,
        if_neg hj_ne_p, if_neg hj_ne_i]
    ring

/-- **Math.** For an orthogonal `n × n` matrix `M` whose last row is the standard basis
vector `e_{n-1}ᵀ`, the last column is `e_{n-1}`. -/
private theorem last_col_eq_e_n_of_orthogonal (hn : 1 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ) (hortho : M.IsOrthogonal)
    (hrow : ∀ j : Fin n,
      M ⟨n - 1, by omega⟩ j = if j = ⟨n - 1, by omega⟩ then 1 else 0) :
    ∀ i : Fin n,
      M i ⟨n - 1, by omega⟩ = if i = ⟨n - 1, by omega⟩ then 1 else 0 := by
  intro i
  -- (M · Mᵀ)[i, n-1] = δ_{i, n-1} from orthogonality.
  have hMMt : M * Mᵀ = 1 := hortho.mul_self_transpose
  have h := congrArg (fun A : Matrix _ _ _ => A i ⟨n - 1, by omega⟩) hMMt
  simp only [Matrix.one_apply] at h
  rw [Matrix.mul_apply] at h
  simp only [Matrix.transpose_apply] at h
  -- Substitute hrow inside the sum and collapse to the (k = n-1) term.
  have hsum : (∑ k : Fin n, M i k * M ⟨n - 1, by omega⟩ k)
      = M i ⟨n - 1, by omega⟩ := by
    calc (∑ k : Fin n, M i k * M ⟨n - 1, by omega⟩ k)
        = ∑ k : Fin n, M i k * (if k = ⟨n - 1, by omega⟩ then 1 else 0) := by
          apply Finset.sum_congr rfl
          intros k _; rw [hrow k]
      _ = M i ⟨n - 1, by omega⟩ := by
          rw [Finset.sum_eq_single ⟨n - 1, by omega⟩]
          · simp
          · intros b _ hb; simp [hb]
          · simp
  rw [hsum] at h
  exact h

/-- **Math.** For an orthogonal upper Hessenberg `n × n` matrix `M` (`n ≥ 2`) whose
last row equals `e_{n-1}ᵀ`, the principal `(n - 1) × (n - 1)` top-left
submatrix is itself orthogonal upper Hessenberg.

The orthogonality of the corner is forced by the row hypothesis alone: it
makes the last column of the contributions to `(M'ᵀ M')[i, j]` vanish, so the
restricted sum equals the full orthogonality identity. The corresponding
column hypothesis is therefore not required here. -/
private theorem block_decomposition (hn : 2 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hortho : M.IsOrthogonal) (hhess : M.IsUpperHessenberg)
    (hrow : ∀ j : Fin n,
      M ⟨n - 1, by omega⟩ j = if j = ⟨n - 1, by omega⟩ then 1 else 0) :
    let f : Fin (n - 1) → Fin n := Fin.castLE (Nat.sub_le n 1)
    let M' : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ := M.submatrix f f
    M'.IsOrthogonal ∧ M'.IsUpperHessenberg := by
  intro f M'
  -- f is value-preserving: (f k).val = k.val.
  have hf_val : ∀ k : Fin (n - 1), (f k).val = k.val := fun _ => rfl
  -- f is injective.
  have hf_inj : Function.Injective f := Fin.castLE_injective _
  -- f never hits ⟨n-1, _⟩ since k.val < n - 1.
  have hf_ne : ∀ k : Fin (n - 1), f k ≠ ⟨n - 1, by omega⟩ := fun k h => by
    have hkv := k.isLt
    have := congrArg Fin.val h
    simp [hf_val] at this; omega
  refine ⟨?_, ?_⟩
  · -- Orthogonality. Show (M'ᵀ * M')[i, j] = δ_{i, j} entry-by-entry.
    change M'ᵀ * M' = 1
    ext i j
    -- Reduce to a sum identity.
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    -- Use full orthogonality at (f i, f j).
    have hfull := congrArg (fun A : Matrix _ _ _ => A (f i) (f j)) hortho
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hfull
    -- hfull : ∑ k : Fin n, M k (f i) * M k (f j) = if f i = f j then 1 else 0
    -- Convert RHS: f i = f j ↔ i = j (since f is injective).
    have hif_eq : (if (f i = f j) then (1 : ℝ) else 0) = if i = j then 1 else 0 := by
      by_cases h : i = j
      · simp [h]
      · have h' : f i ≠ f j := fun he => h (hf_inj he)
        rw [if_neg h, if_neg h']
    rw [hif_eq] at hfull
    -- Split the Fin n sum into Fin (n-1) image + the singleton {⟨n-1, _⟩}.
    -- The singleton term has factor M[⟨n-1, _⟩, f i] = 0 (by hrow + hf_ne).
    have hM_top : M ⟨n - 1, by omega⟩ (f i) = 0 := by
      rw [hrow (f i), if_neg (hf_ne i)]
    -- Define the Fin (n-1) → Fin n embedding as a Finset.embedding.
    -- Sum partition: ∑ k : Fin n = ∑ over image f + the missing element.
    rw [show (∑ k : Fin n, M k (f i) * M k (f j))
          = (∑ k : Fin (n - 1), M (f k) (f i) * M (f k) (f j))
            + M ⟨n - 1, by omega⟩ (f i) * M ⟨n - 1, by omega⟩ (f j) from ?_] at hfull
    · rw [hM_top, zero_mul, add_zero] at hfull; exact hfull
    -- Prove the sum split.
    -- Bijection: φ : Option (Fin (n-1)) → Fin n, sending none ↦ ⟨n-1, _⟩, some k ↦ f k.
    -- We use Finset.sum_bij from `(univ : Finset (Fin n))` to `insert none (univ.image some)`.
    -- Easier: use Finset.sum_insert and Finset.sum_bij separately.
    have hpartition : (Finset.univ : Finset (Fin n)) =
        insert ⟨n - 1, by omega⟩
          ((Finset.univ : Finset (Fin (n - 1))).attach.image (fun a => f a.1)) := by
      ext k
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_attach,
        Finset.mem_univ, true_and]
      constructor
      · intro _
        by_cases hk : k.val = n - 1
        · left; exact Fin.ext hk
        · right; exact ⟨⟨⟨k.val, by have := k.isLt; omega⟩, Finset.mem_univ _⟩,
            by ext; rfl⟩
      · rintro (rfl | ⟨⟨a, _⟩, rfl⟩)
        · trivial
        · trivial
    have hnotmem : (⟨n - 1, by omega⟩ : Fin n) ∉
        ((Finset.univ : Finset (Fin (n - 1))).attach.image (fun a => f a.1)) := by
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      rintro ⟨a, _, ha⟩
      exact hf_ne a ha
    rw [hpartition, Finset.sum_insert hnotmem,
        Finset.sum_image (fun ⟨a, _⟩ _ ⟨b, _⟩ _ hab => by
          have : f a = f b := hab
          have := hf_inj this
          ext; exact congrArg Fin.val this)]
    -- ∑ over attach.image = ∑ over univ via Finset.sum_attach
    rw [Finset.sum_attach (Finset.univ : Finset (Fin (n - 1)))
          (fun k => M (f k) (f i) * M (f k) (f j))]
    ring
  · -- Hessenberg.
    intros i j hij
    change M (f i) (f j) = 0
    exact hhess (f i) (f j) (by rw [hf_val, hf_val]; exact hij)

/-- **Math.** Right-multiplying an upper Hessenberg matrix by the transpose of the Givens
rotation at the rightmost interface preserves upper Hessenberg. Used in the
universality proof to verify that `Q · G(θ)ᵀ` remains Hessenberg when peeling
off the last column. -/
private theorem mul_givens_transpose_isUpperHessenberg (hn : 2 ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hhess : Q.IsUpperHessenberg) (θ : ℝ) :
    (Q * (givensRotation n ⟨n - 2, by omega⟩ θ)ᵀ).IsUpperHessenberg := by
  intros i j hij
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  -- `j + 1 < i ≤ n - 1` forces `j < n - 2`, so `j ∉ {n-2, n-1}`.
  have hj_ne_n2 : j.val ≠ n - 2 := by have := i.isLt; omega
  have hj_ne_n1 : j.val ≠ n - 2 + 1 := by have := i.isLt; omega
  have hGj : ∀ x, givensRotation n ⟨n - 2, by omega⟩ θ j x = if j = x then 1 else 0 :=
    fun x => givensRotation.apply_of_ne_row ⟨n - 2, by omega⟩ θ j x hj_ne_n2 hj_ne_n1
  simp_rw [hGj, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ j fun x => Q i x]
  rw [if_pos (Finset.mem_univ _)]
  exact hhess i j hij

/-! ### Base cases of the universality induction

The `n = 0` and `n = 1` cases of `exists_givensFactorization_aux` are
small in size but structurally distinct from the inductive step (no
peeling, no block decomposition). Pulling them out as named lemmas keeps
the inductive case readable and exposes them for direct reuse. -/

/-- **Math.** Base case `n = 0`: the empty matrix is trivially `SignEquiv` to the
empty Givens product via reflexivity. -/
private lemma exists_givensFactorization_zero (Q : Matrix (Fin 0) (Fin 0) ℝ) :
    ∃ θ : Fin (0 - 1) → ℝ, SignEquiv Q (givensProduct θ) :=
  ⟨Fin.elim0, SignEquiv.refl _⟩

/-- **Mixed.** Base case `n = 1`: a 1×1 orthogonal matrix has `Q[0,0] = ±1`, so
`SignEquiv Q 1` via `D_L = diag(Q[0,0])`, `D_R = 1`, and the empty
Givens product is `1`. -/
private lemma exists_givensFactorization_one (Q : Matrix (Fin 1) (Fin 1) ℝ)
    (hortho : Q.IsOrthogonal) :
    ∃ θ : Fin (1 - 1) → ℝ, SignEquiv Q (givensProduct θ) := by
  have h00sq : Q 0 0 * Q 0 0 = 1 := by
    have h := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℝ => A 0 0) hortho
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply]
      using h
  refine ⟨Fin.elim0, diagonal (fun _ => Q 0 0), diagonal (fun _ => 1),
    ⟨fun _ => Q 0 0, ?_, rfl⟩, ⟨fun _ => 1, fun _ => Or.inl rfl, rfl⟩, ?_⟩
  · intro _
    rcases mul_self_eq_one_iff.mp h00sq with h | h
    · exact Or.inl h
    · exact Or.inr h
  · unfold givensProduct
    simp only [Nat.sub_self, List.ofFn_zero, List.prod_nil]
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply]
    linarith

/-! ### Inductive step: eliminate-last-row (Step 1) -/

/-! ## Mixed — Math: pick a Givens angle `θ₀` whose `(cos, sin)` matches the
    last row's two non-zero entries, so right-multiplication by `G(θ₀)ᵀ`
    sends the last row of `Q` to `e_{n-1}ᵀ` while preserving orthogonality
    and upper-Hessenberg. | Eng: bundles `last_row_norm` (unit-norm of the
    last row), `exists_angle_for_last_row` (cos/sin construction),
    `mul_givens_last_clears` (the row-clearing identity),
    `mul_givens_transpose_isUpperHessenberg`, and `IsOrthogonal.mul`. -/

/-- **Mixed.** **Step 1 of the inductive Givens factorization** (last-row elimination):
for orthogonal upper Hessenberg `Q` of size `n ≥ 2`, there is a Givens angle
`θ₀` such that `M' := Q · G(θ₀)ᵀ` (with `G := givensRotation n ⟨n-2, _⟩ θ₀`)
is again orthogonal upper Hessenberg, with last row equal to the standard
basis vector `e_{n-1}ᵀ`. -/
private lemma eliminate_last_row (n : ℕ) (hn : 2 ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hortho : Q.IsOrthogonal)
    (hhess : Q.IsUpperHessenberg) :
    ∃ θ₀ : ℝ,
      (Q * (givensRotation n ⟨n - 2, by omega⟩ θ₀)ᵀ).IsOrthogonal ∧
      (Q * (givensRotation n ⟨n - 2, by omega⟩ θ₀)ᵀ).IsUpperHessenberg ∧
      ∀ j : Fin n,
        (Q * (givensRotation n ⟨n - 2, by omega⟩ θ₀)ᵀ) ⟨n - 1, by omega⟩ j
          = if j = ⟨n - 1, by omega⟩ then 1 else 0 := by
  have hnorm := last_row_norm hn Q hortho hhess
  obtain ⟨θ₀, hcos, hsin⟩ := exists_angle_for_last_row
    (Q ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩)
    (Q ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩) hnorm
  refine ⟨θ₀, ?_, ?_, ?_⟩
  · exact IsOrthogonal.mul hortho (givensRotation_isOrthogonal _ _).transpose
  · exact mul_givens_transpose_isUpperHessenberg hn Q hhess θ₀
  · exact mul_givens_last_clears hn Q hortho hhess θ₀ hcos hsin

/-! ### Inductive step: assembly tools -/

/-! ## Mathematical layer — pure tool: a `±1`-valued function on
    `Fin (k' + 1)` extended at the boundary index by another `±1` value
    is again `±1`-valued on `Fin (k' + 1 + 1)`. -/

/-- **Math.** Extending a `±1`-valued function `d : Fin (k' + 1) → ℝ` by a `±1` value
`boundary` at the index `k' + 1` (in `Fin (k' + 1 + 1)`) yields a function
whose every value is again `±1`. Used to verify that the assembled
`d_{L,full}` and `d_{R,full}` diagonals in `assemble_factorization` are
both `±1`-valued. -/
private lemma boundaryAppended_diag_isPlusMinusOne {k' : ℕ}
    (d : Fin (k' + 1) → ℝ) (boundary : ℝ)
    (hd : ∀ i, d i = 1 ∨ d i = -1) (hb : boundary = 1 ∨ boundary = -1)
    (i : Fin (k' + 1 + 1)) :
    (if h : i.val < k' + 1 then d ⟨i.val, h⟩ else boundary) = 1 ∨
    (if h : i.val < k' + 1 then d ⟨i.val, h⟩ else boundary) = -1 := by
  by_cases hi : i.val < k' + 1
  · simp only [hi, dif_pos]; exact hd ⟨i.val, hi⟩
  · simp only [hi, dif_neg, not_false_iff]; exact hb

/-! ## Mixed — Math: the Givens rotation `G(θ₀)` at plane `(k', k' + 1)`
    commutes with a diagonal whose two boundary values agree (i.e. with the
    "extended diagonal" produced by `assemble_factorization` from `d_R'`).
    | Eng: thin wrapper over
    `givensRotation_commute_diagonal_of_eq_on_rotation_pair`; the equality
    on the rotation pair is the
    `dif_pos / dif_neg` simplification of the extended diagonal at indices
    `⟨k', _⟩` and `⟨k' + 1, _⟩`. -/

/-- **Mixed.** **Step 2 of the assembly**: the Givens rotation
`G(θ₀) := givensRotation (k' + 2) ⟨k', _⟩ θ₀` commutes with the extended
diagonal whose corner part is `d : Fin (k' + 1) → ℝ` and whose boundary
value is `d ⟨k', _⟩`, because the extended diagonal is constant on the
`(k', k' + 1)` rotation pair. -/
private lemma givensRotation_commutes_with_boundaryAppended_diag {k' : ℕ}
    (θ₀ : ℝ) (d : Fin (k' + 1) → ℝ) :
    givensRotation (k' + 1 + 1) (⟨k', by omega⟩ : Fin (k' + 1)) θ₀ *
      Matrix.diagonal (fun i : Fin (k' + 1 + 1) =>
        if h : i.val < k' + 1 then d ⟨i.val, h⟩ else d ⟨k', by omega⟩) =
    Matrix.diagonal (fun i : Fin (k' + 1 + 1) =>
        if h : i.val < k' + 1 then d ⟨i.val, h⟩ else d ⟨k', by omega⟩) *
    givensRotation (k' + 1 + 1) (⟨k', by omega⟩ : Fin (k' + 1)) θ₀ := by
  apply givensRotation_commute_diagonal_of_eq_on_rotation_pair
  change (if h : k' < k' + 1 then d ⟨k', h⟩ else d ⟨k', by omega⟩) =
    (if h : k' + 1 < k' + 1 then d ⟨k' + 1, h⟩ else d ⟨k', by omega⟩)
  rw [dif_pos (by omega : k' < k' + 1),
      dif_neg (by omega : ¬ k' + 1 < k' + 1)]

/-! ## Mixed — Math: peel the last factor off
    `givensProduct (θ_full)` where `θ_full` extends `θ' : Fin k' → ℝ` at the
    boundary by the angle `θ₀`; the result is the `k'`-factor partial
    product (in ambient dimension `k' + 2`) times the boundary Givens
    rotation `G(θ₀)`. | Eng: `List.ofFn_succ_last` peeling, `congr 1` on
    each factor, `dif_pos` / `dif_neg` to dispatch the conditional in the
    interior vs boundary indices. -/

/-- **Mixed.** **Step 3 of the assembly**: the canonical Givens product over the
extended angle vector
`θ_full := fun i => if i.val < k' then θ' ⟨i.val, _⟩ else θ₀`
peels into the `k'`-factor partial product of `θ'` (in ambient dimension
`k' + 2`) followed by the boundary Givens rotation `G(θ₀)`. -/
private lemma givensProduct_peel_last {k' : ℕ}
    (θ' : Fin k' → ℝ) (θ₀ : ℝ) :
    givensProduct (fun i : Fin (k' + 1 + 1 - 1) =>
        if h : i.val < k' then θ' ⟨i.val, h⟩ else θ₀) =
      partialGivensProduct (n := k' + 2) (m := k') (by omega) θ' *
      givensRotation (k' + 1 + 1) (⟨k', by omega⟩ : Fin (k' + 1)) θ₀ := by
  change (List.ofFn fun i : Fin (k' + 1) =>
      givensRotation (k' + 1 + 1) i
        ((fun j : Fin (k' + 1 + 1 - 1) =>
          if h : j.val < k' then θ' ⟨j.val, h⟩ else θ₀) i)).prod = _
  rw [List.ofFn_succ_last, List.prod_append, List.prod_singleton]
  congr 1
  · -- Partial: identify with `partialGivensProduct`.
    unfold partialGivensProduct
    congr 1
    congr 1
    funext t
    simp only [Fin.val_castSucc]
    rw [dif_pos (by have := t.isLt; omega : t.val < k')]
    rfl
  · -- Last factor: index `Fin.last k' = ⟨k', _⟩`, value `θ₀`.
    show givensRotation (k' + 1 + 1) (Fin.last k')
        ((fun j : Fin (k' + 1 + 1 - 1) =>
          if h : j.val < k' then θ' ⟨j.val, h⟩ else θ₀) (Fin.last k')) =
      givensRotation (k' + 1 + 1) (⟨k', by omega⟩ : Fin (k' + 1)) θ₀
    simp only [Fin.val_last]
    rw [dif_neg (by omega : ¬ k' < k')]
    rfl

/-! ## Mixed — Math: **Steps 4–5 of the assembly** (corner extension).
    The `k'`-factor partial product of `θ'` in ambient dimension `k' + 2`
    equals `D_{L,full} · M' · D_{R,full}` (the assembled diagonals applied
    to `M' := Q · G(θ₀)ᵀ`). The proof is entry-wise: corner entries
    `(i, j)` with both indices `< k' + 1` reduce to the IH equation
    `givensProduct θ' = D_{L'} · M'' · D_{R'}`; boundary entries (last row
    or last column of `M'`) vanish thanks to `M'`'s `e_{k'+1}ᵀ` last row
    and the orthogonality-induced `e_{k'+1}` last column. | Eng: `ext i j`
    + 4-way `by_cases` on `(i.val < k' + 1, j.val < k' + 1)`; boundary
    branches use `partialGivensProduct_apply_of_{row,col}_ge` to identify
    `P` with the identity row/column; corner branch extracts the IH
    submatrix entry via `partialGivensProduct_corner` and a
    `Matrix.submatrix_apply` defeq. -/

/-- **Mixed.** **Steps 4–5 of the assembly**: under the Step-1 hypotheses on
`M' := Q · G(θ₀)ᵀ` (orthogonal, last row `e_{k'+1}ᵀ`) and the IH equation
`givensProduct θ' = D_{L'} · M'' · D_{R'}` for `M''` the principal
`(k' + 1) × (k' + 1)` corner of `M'`, the partial Givens product of `θ'`
in ambient dimension `k' + 2` equals
`D_{L,full} · M' · D_{R,full}`, where the assembled diagonals extend
`d_L'` / `d_R'` by `d_R' ⟨k', _⟩` at the boundary index. -/
private lemma partialProduct_eq_diagonals_mul_M {k' : ℕ}
    (Q : Matrix (Fin (k' + 1 + 1)) (Fin (k' + 1 + 1)) ℝ) (θ₀ : ℝ)
    (hM'_ortho : (Q *
        (givensRotation (k' + 1 + 1) ⟨k', by omega⟩ θ₀)ᵀ).IsOrthogonal)
    (hM'_lastrow : ∀ j : Fin (k' + 1 + 1),
      (Q * (givensRotation (k' + 1 + 1) ⟨k', by omega⟩ θ₀)ᵀ)
        ⟨k' + 1, by omega⟩ j
        = if j = ⟨k' + 1, by omega⟩ then 1 else 0)
    (θ' : Fin k' → ℝ) (d_L' d_R' : Fin (k' + 1) → ℝ)
    (hdR' : ∀ i, d_R' i = 1 ∨ d_R' i = -1)
    (hSEeq : givensProduct (n := k' + 1) θ' = Matrix.diagonal d_L' *
        (Q * (givensRotation (k' + 1 + 1) ⟨k', by omega⟩ θ₀)ᵀ).submatrix
          (Fin.castLE (Nat.le_succ (k' + 1))) (Fin.castLE (Nat.le_succ (k' + 1))) *
        Matrix.diagonal d_R') :
    partialGivensProduct (n := k' + 2) (m := k') (by omega) θ' =
      Matrix.diagonal (fun i : Fin (k' + 1 + 1) =>
        if h : i.val < k' + 1 then d_L' ⟨i.val, h⟩ else d_R' ⟨k', by omega⟩) *
      (Q * (givensRotation (k' + 1 + 1) ⟨k', by omega⟩ θ₀)ᵀ) *
      Matrix.diagonal (fun i : Fin (k' + 1 + 1) =>
        if h : i.val < k' + 1 then d_R' ⟨i.val, h⟩ else d_R' ⟨k', by omega⟩) := by
  set M' : Matrix (Fin (k' + 1 + 1)) (Fin (k' + 1 + 1)) ℝ :=
    Q * (givensRotation (k' + 1 + 1) ⟨k', by omega⟩ θ₀)ᵀ
  let f : Fin (k' + 1) → Fin (k' + 1 + 1) := Fin.castLE (Nat.le_succ (k' + 1))
  let M'' : Matrix (Fin (k' + 1)) (Fin (k' + 1)) ℝ := M'.submatrix f f
  set d_L_full : Fin (k' + 1 + 1) → ℝ :=
    fun i => if h : i.val < k' + 1 then d_L' ⟨i.val, h⟩ else d_R' ⟨k', by omega⟩
    with hd_L_full_def
  set d_R_full : Fin (k' + 1 + 1) → ℝ :=
    fun i => if h : i.val < k' + 1 then d_R' ⟨i.val, h⟩ else d_R' ⟨k', by omega⟩
    with hd_R_full_def
  set P : Matrix (Fin (k' + 1 + 1)) (Fin (k' + 1 + 1)) ℝ :=
    partialGivensProduct (n := k' + 2) (m := k') (by omega) θ' with hP_def
  -- Step 5 body: ext + 4-way case split.
  have hM'_lastcol : ∀ i : Fin (k' + 1 + 1),
      M' i ⟨k' + 1, by omega⟩ = if i = ⟨k' + 1, by omega⟩ then 1 else 0 :=
    last_col_eq_e_n_of_orthogonal (by omega) M' hM'_ortho
      (fun j => by have := hM'_lastrow j; convert this using 2)
  ext i j
  rw [show (Matrix.diagonal d_L_full * M' * Matrix.diagonal d_R_full) i j
        = d_L_full i * M' i j * d_R_full j from by
    simp [Matrix.mul_apply, Matrix.diagonal_apply, mul_comm,
          Finset.sum_ite_eq, Finset.sum_ite_eq']]
  have hP_inline : P = (List.ofFn fun t : Fin k' =>
      givensRotation (k' + 1 + 1) ⟨t.val, by omega⟩ (θ' t)).prod := by
    change partialGivensProduct (n := k' + 2) (m := k') (by omega) θ' = _
    unfold partialGivensProduct; rfl
  let θP : Fin (k' + 1 + 1 - 1) → ℝ := fun t =>
    if h : t.val < k' + 1 - 1 then θ' ⟨t.val, h⟩ else 0
  have hθP_eq : ∀ t : Fin k', θP ⟨t.val, by omega⟩ = θ' t := by
    intro t
    change (if h : t.val < k' + 1 - 1 then θ' ⟨t.val, h⟩ else 0) = θ' t
    rw [dif_pos (show t.val < k' + 1 - 1 by have := t.isLt; omega)]
  have hP_inline' : P = (List.ofFn fun t : Fin k' =>
      givensRotation (k' + 1 + 1) ⟨t.val, by omega⟩
        (θP ⟨t.val, by omega⟩)).prod := by
    rw [hP_inline]; simp_rw [hθP_eq]
  have hM'_col_zero : ∀ (a : ℕ) (ha : a < k' + 1 + 1) (hlt : a < k' + 1),
      M' ⟨a, ha⟩ ⟨k' + 1, by omega⟩ = 0 := by
    intro a ha hlt
    rw [hM'_lastcol]
    have h_ne : (⟨a, ha⟩ : Fin (k' + 1 + 1)) ≠ ⟨k' + 1, by omega⟩ := by
      intro h; injection h with hv; omega
    rw [if_neg h_ne]
  have hM'_row_zero : ∀ (b : ℕ) (hb : b < k' + 1 + 1) (hlt : b < k' + 1),
      M' ⟨k' + 1, by omega⟩ ⟨b, hb⟩ = 0 := by
    intro b hb hlt
    have hlr := hM'_lastrow ⟨b, hb⟩
    have h_ne : (⟨b, hb⟩ : Fin (k' + 1 + 1)) ≠ ⟨k' + 1, by omega⟩ := by
      intro h; injection h with hv; omega
    rw [if_neg h_ne] at hlr
    exact hlr
  have hM'_corner_one : M' ⟨k' + 1, by omega⟩ ⟨k' + 1, by omega⟩ = 1 := by
    have hlr := hM'_lastrow ⟨k' + 1, by omega⟩
    rw [if_pos rfl] at hlr
    exact hlr
  by_cases hi_lt : i.val < k' + 1
  · by_cases hj_lt : j.val < k' + 1
    · -- Case A: both in Fin (k'+1) corner. Use Lemma 2 + IH.
      simp only [hd_L_full_def, hd_R_full_def]
      rw [dif_pos hi_lt, dif_pos hj_lt]
      have hP_corner : P i j = givensProduct (n := k' + 1) θ' ⟨i.val, hi_lt⟩
          ⟨j.val, hj_lt⟩ := by
        rw [hP_def]
        have := congrArg (fun A : Matrix (Fin (k' + 1)) (Fin (k' + 1)) ℝ =>
            A ⟨i.val, hi_lt⟩ ⟨j.val, hj_lt⟩) (partialGivensProduct_corner θ')
        simp only [Matrix.submatrix_apply] at this
        have hi_cast : (Fin.castLE (Nat.le_succ (k' + 1)) ⟨i.val, hi_lt⟩
            : Fin (k' + 1 + 1)) = i := Fin.ext rfl
        have hj_cast : (Fin.castLE (Nat.le_succ (k' + 1)) ⟨j.val, hj_lt⟩
            : Fin (k' + 1 + 1)) = j := Fin.ext rfl
        rw [hi_cast, hj_cast] at this
        exact this
      rw [hP_corner, hSEeq]
      have hLHS : (Matrix.diagonal d_L' * M'' * Matrix.diagonal d_R')
          ⟨i.val, hi_lt⟩ ⟨j.val, hj_lt⟩
          = d_L' ⟨i.val, hi_lt⟩ * M'' ⟨i.val, hi_lt⟩ ⟨j.val, hj_lt⟩
            * d_R' ⟨j.val, hj_lt⟩ := by
        simp [Matrix.mul_apply, Matrix.diagonal_apply, mul_comm,
              Finset.sum_ite_eq, Finset.sum_ite_eq']
      rw [hLHS]
      have hM'' : M'' ⟨i.val, hi_lt⟩ ⟨j.val, hj_lt⟩ = M' i j := by
        change M'.submatrix f f ⟨i.val, hi_lt⟩ ⟨j.val, hj_lt⟩ = M' i j
        simp only [Matrix.submatrix_apply]
        rfl
      rw [hM'']
    · -- Case B: i.val < k'+1, j.val = k'+1.
      push_neg at hj_lt
      have hj_eq : j = ⟨k' + 1, by omega⟩ := by
        ext; change j.val = k' + 1; have := j.isLt; omega
      rw [hj_eq]
      rw [hM'_col_zero i.val (by have := i.isLt; omega) hi_lt]
      rw [hP_inline']
      rw [partialGivensProduct_apply_of_col_ge (n := k' + 1 + 1) θP k'
          (by omega) ⟨k' + 1, by omega⟩ (by omega) i]
      rw [if_neg (fun h => by
        have : i.val = k' + 1 := by rw [h]
        omega)]
      ring
  · push_neg at hi_lt
    have hi_eq : i = ⟨k' + 1, by omega⟩ := by
      ext; change i.val = k' + 1; have := i.isLt; omega
    by_cases hj_lt : j.val < k' + 1
    · -- Case C: i.val = k'+1, j.val < k'+1.
      rw [hi_eq]
      rw [hM'_row_zero j.val (by have := j.isLt; omega) hj_lt]
      rw [hP_inline']
      rw [partialGivensProduct_apply_of_row_ge (n := k' + 1 + 1) θP k'
          (by omega) ⟨k' + 1, by omega⟩ j (by omega)]
      rw [if_neg (fun h => by
        have : j.val = k' + 1 := by rw [← h]
        omega)]
      ring
    · -- Case D: i = j = ⟨k'+1⟩.
      push_neg at hj_lt
      have hj_eq : j = ⟨k' + 1, by omega⟩ := by
        ext; change j.val = k' + 1; have := j.isLt; omega
      rw [hi_eq, hj_eq, hM'_corner_one]
      simp only [hd_L_full_def, hd_R_full_def]
      rw [dif_neg (Nat.lt_irrefl (k' + 1)),
          dif_neg (Nat.lt_irrefl (k' + 1))]
      rw [hP_inline']
      rw [partialGivensProduct_apply_of_row_ge (n := k' + 1 + 1) θP k'
          (by omega) ⟨k' + 1, by omega⟩ ⟨k' + 1, by omega⟩ (by omega)]
      rw [if_pos rfl]
      rcases hdR' ⟨k', by omega⟩ with h | h <;> rw [h] <;> ring

/-! ### Inductive step: assemble-factorization (Steps 2–5 driver) -/

/-! ## Mathematical layer — assembly driver. Bundles the four assembly
    tools above into the SignEquiv triple `(θ_full, d_{L,full}, d_{R,full})`
    plus the matrix equation. The math skeleton is visible end-to-end:
    extend the diagonals, build the angle vector, then derive the matrix
    equation by the algebraic chain hQ → hpeel → hP → hcomm. -/

/-- **Math.** **Steps 2–5 of the inductive Givens factorization** (assembly +
verification): given `Q : Matrix (Fin (k' + 2)) (Fin (k' + 2)) ℝ`, the
Step-1 angle `θ₀` (so `M' := Q · G(θ₀)ᵀ` has the last row `e_{k'+1}ᵀ`),
and the IH applied to the principal `(k' + 1) × (k' + 1)` corner `M''` of
`M'` (yielding angles `θ'` and `±1`-diagonals `d_L', d_R'` with
`givensProduct θ' = D_{L'} · M'' · D_{R'}`), construct full angles and
diagonals exhibiting `SignEquiv Q (givensProduct θ_full)`. -/
private lemma assemble_factorization {k' : ℕ}
    (Q : Matrix (Fin (k' + 1 + 1)) (Fin (k' + 1 + 1)) ℝ) (θ₀ : ℝ)
    (hM'_ortho : (Q *
        (givensRotation (k' + 1 + 1) ⟨k', by omega⟩ θ₀)ᵀ).IsOrthogonal)
    (hM'_lastrow : ∀ j : Fin (k' + 1 + 1),
      (Q * (givensRotation (k' + 1 + 1) ⟨k', by omega⟩ θ₀)ᵀ)
        ⟨k' + 1, by omega⟩ j
        = if j = ⟨k' + 1, by omega⟩ then 1 else 0)
    (θ' : Fin k' → ℝ) (d_L' d_R' : Fin (k' + 1) → ℝ)
    (hdL' : ∀ i, d_L' i = 1 ∨ d_L' i = -1)
    (hdR' : ∀ i, d_R' i = 1 ∨ d_R' i = -1)
    (hSEeq : givensProduct (n := k' + 1) θ' = Matrix.diagonal d_L' *
        (Q * (givensRotation (k' + 1 + 1) ⟨k', by omega⟩ θ₀)ᵀ).submatrix
          (Fin.castLE (Nat.le_succ (k' + 1))) (Fin.castLE (Nat.le_succ (k' + 1))) *
        Matrix.diagonal d_R') :
    ∃ θ : Fin (k' + 1 + 1 - 1) → ℝ, SignEquiv Q (givensProduct θ) := by
  refine ⟨fun i => if h : i.val < k' then θ' ⟨i.val, h⟩ else θ₀,
          Matrix.diagonal (fun i => if h : i.val < k' + 1 then d_L' ⟨i.val, h⟩
                   else d_R' ⟨k', by omega⟩),
          Matrix.diagonal (fun i => if h : i.val < k' + 1 then d_R' ⟨i.val, h⟩
                   else d_R' ⟨k', by omega⟩),
          ⟨fun i => if h : i.val < k' + 1 then d_L' ⟨i.val, h⟩
                   else d_R' ⟨k', by omega⟩, ?_, rfl⟩,
          ⟨fun i => if h : i.val < k' + 1 then d_R' ⟨i.val, h⟩
                   else d_R' ⟨k', by omega⟩, ?_, rfl⟩,
          ?_⟩
  · intro i
    exact boundaryAppended_diag_isPlusMinusOne d_L' (d_R' ⟨k', by omega⟩) hdL'
      (hdR' ⟨k', by omega⟩) i
  · intro i
    exact boundaryAppended_diag_isPlusMinusOne d_R' (d_R' ⟨k', by omega⟩) hdR'
      (hdR' ⟨k', by omega⟩) i
  · -- Matrix equation: chain hQ → hpeel → hP → hcomm.
    set G : Matrix (Fin (k' + 1 + 1)) (Fin (k' + 1 + 1)) ℝ :=
      givensRotation (k' + 1 + 1) ⟨k', by omega⟩ θ₀ with hG_def
    set M' : Matrix (Fin (k' + 1 + 1)) (Fin (k' + 1 + 1)) ℝ := Q * Gᵀ with hM'_def
    have hG_ortho : G.IsOrthogonal := givensRotation_isOrthogonal _ _
    have hQ : Q = M' * G := by
      change Q = (Q * Gᵀ) * G
      rw [Matrix.mul_assoc, show Gᵀ * G = 1 from hG_ortho, Matrix.mul_one]
    have hcomm := givensRotation_commutes_with_boundaryAppended_diag (k' := k') θ₀ d_R'
    have hpeel := givensProduct_peel_last (k' := k') θ' θ₀
    have hP := partialProduct_eq_diagonals_mul_M (k' := k') Q θ₀ hM'_ortho
      hM'_lastrow θ' d_L' d_R' hdR' hSEeq
    rw [hpeel, hP, ← hM'_def]
    rw [hQ]
    rw [Matrix.mul_assoc (Matrix.diagonal _ * M') (Matrix.diagonal _) G,
        ← hcomm,
        ← Matrix.mul_assoc, Matrix.mul_assoc (Matrix.diagonal _)]

/-- **Math.** Auxiliary: universality of Givens factorization for *any* `n ≥ 0`.
The user-facing version `exists_givensFactorization` (with `2 ≤ n`)
specialises this. -/
theorem exists_givensFactorization_aux :
    ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ),
      Q.IsOrthogonal → Q.IsUpperHessenberg →
      ∃ θ : Fin (n - 1) → ℝ, SignEquiv Q (givensProduct θ) := by
  intro n
  induction n with
  | zero => intros Q _ _; exact exists_givensFactorization_zero Q
  | succ k ih =>
    intros Q hortho hhess
    by_cases hk : k = 0
    · subst hk; exact exists_givensFactorization_one Q hortho
    · -- n = k + 1 ≥ 2. Substitute k = k' + 1 to make `Fin (k - 1) = Fin k'`
      -- definitional, then chain Step 1 (eliminate_last_row), the IH on the
      -- block-decomposed corner, and Steps 2–5 (assemble_factorization).
      have hk_ge_1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hn : 2 ≤ k + 1 := by omega
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 :=
        ⟨k - 1, (Nat.sub_add_cancel hk_ge_1).symm⟩
      obtain ⟨θ₀, hM'_ortho, hM'_hess, hM'_lastrow⟩ :=
        eliminate_last_row (k' + 1 + 1) hn Q hortho hhess
      obtain ⟨hM''_ortho, hM''_hess⟩ :=
        block_decomposition hn _ hM'_ortho hM'_hess hM'_lastrow
      obtain ⟨θ', _, _, ⟨d_L', hdL', rfl⟩, ⟨d_R', hdR', rfl⟩, hSEeq⟩ :=
        ih _ hM''_ortho hM''_hess
      exact assemble_factorization Q θ₀ hM'_ortho hM'_lastrow
        θ' d_L' d_R' hdL' hdR' hSEeq

/-- **Math.** **Universality of the canonical Givens factorization**: every orthogonal
upper Hessenberg `n × n` real matrix is sign-equivalent to `givensProduct θ`
for some choice of angles `θ : Fin (n - 1) → ℝ`.

This is the converse direction to `givensProduct_isUpperHessenberg`: where
that lemma says every canonical Givens product is upper Hessenberg, this
lemma says every (orthogonal) upper Hessenberg matrix arises — modulo a
left/right diagonal sign flip — from such a product. -/
private theorem exists_givensFactorization
    (Q : Matrix (Fin n) (Fin n) ℝ)
    (hortho : Q.IsOrthogonal)
    (hhess : Q.IsUpperHessenberg) :
    ∃ θ : Fin (n - 1) → ℝ, SignEquiv Q (givensProduct θ) :=
  exists_givensFactorization_aux n Q hortho hhess

end Matrix

namespace HessenbergDigraphs

/-! ## Mathematical layer — bundled-structure form of universality
    (Severini Lemma 1 + paper Theorem 1): every bundled
    `OrthogonalHessenberg n` arises (up to sign equivalence) from the
    canonical Givens product of some angle vector. -/

open scoped HessenbergDigraphs in
/-- **Math.** bundled-structure form (Severini Lemma 1 + paper Theorem 1): every
unreduced `OrthogonalHessenberg n` is sign-equivalent to the canonical
Givens product of some `UnreducedAngles n`. -/
theorem OrthogonalHessenberg.exists_givensFactorization {n : ℕ} (hn : 2 ≤ n)
    (Q : OrthogonalHessenberg n) (hu : Q.IsUnreduced) :
    ∃ θ : UnreducedAngles n, Q ≃sign θ.product := by
  obtain ⟨f, hsign⟩ :=
    Matrix.exists_givensFactorization Q.matrix Q.orthogonal Q.hessenberg
  -- Show f is unreduced: sign-equivalence preserves the support pattern;
  -- Q is unreduced ⇒ subdiagonal of (givensProduct f) non-zero ⇒ sin (f k) ≠ 0.
  have h_f_unred : ∀ k : Fin (n - 1), Real.sin (f k) ≠ 0 := by
    intro k
    have hk_succ : k.val + 1 < n := by have := k.isLt; omega
    have hk_le : k.val < n := by have := k.isLt; omega
    -- Build vertex with value k.val + 1 ∈ [1, n - 1] and apply hu
    set v : Vertex n := ⟨k.val + 1, Nat.succ_le_succ (Nat.zero_le _),
      by have := k.isLt; omega⟩ with hv_def
    have hv_lt : v.value < n := by change k.val + 1 < n; exact hk_succ
    have h_v_subdiag : Q.apply (v.next hv_lt) v ≠ 0 := hu v hv_lt
    -- Translate: Q.apply (v.next hv_lt) v = Q.matrix (v.next hv_lt).toFin v.toFin
    --   (v.next hv_lt).toFin = ⟨k.val + 1, _⟩, v.toFin = ⟨k.val, _⟩
    -- And via SignEquiv preserves_support, this is non-zero iff
    -- givensProduct f at the same Fin pair is non-zero, which equals sin (f k).
    have h_pres :=
      (Matrix.SignEquiv.preserves_support hsign (v.next hv_lt).toFin v.toFin).mp h_v_subdiag
    -- Convert to spine entry of givensProduct
    have h_toFin_v : v.toFin = ⟨k.val, hk_le⟩ := by
      apply Fin.ext; change v.value - 1 = k.val
      change k.val + 1 - 1 = k.val; omega
    have h_toFin_succ : (v.next hv_lt).toFin = ⟨k.val + 1, hk_succ⟩ := by
      apply Fin.ext; change (v.next hv_lt).value - 1 = k.val + 1
      change v.value + 1 - 1 = k.val + 1
      change k.val + 1 + 1 - 1 = k.val + 1; omega
    rw [h_toFin_v, h_toFin_succ] at h_pres
    -- Use the closed form: givensProduct f ⟨k.val + 1⟩ ⟨k.val⟩ = sin (f ⟨k.val⟩)
    have h_sin :=
      Matrix.givensProduct_apply_subdiag_eq_sin f ⟨k.val, hk_le⟩
        (by change k.val + 1 < n; exact hk_succ)
    rw [h_sin] at h_pres
    exact h_pres
  refine ⟨UnreducedAngles.fromFinFunction f h_f_unred, ?_⟩
  change Matrix.SignEquiv Q.matrix _
  -- (fromFinFunction f h_f_unred).product.matrix
  --   = Matrix.givensProduct (fromFinFunction f h_f_unred).toFinFunction
  --   = Matrix.givensProduct f
  rw [show (UnreducedAngles.fromFinFunction f h_f_unred).product.matrix =
        Matrix.givensProduct f from by
          change Matrix.givensProduct (UnreducedAngles.fromFinFunction f h_f_unred).toFinFunction
            = Matrix.givensProduct f
          rw [UnreducedAngles.toFinFunction_fromFinFunction]]
  exact hsign

end HessenbergDigraphs
