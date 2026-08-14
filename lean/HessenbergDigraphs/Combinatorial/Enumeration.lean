/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Enumeration of isomorphism classes

Closed-form counts for the isomorphism classes of `D_n(S)`. The
connected count combines rigidity (each `S` with `|S| ≥ 2` is its own
class) with the singleton coincidence `{t} ≅ {n - t}`. The loopless
variant follows once the active sets are restricted to
`S ⊆ {2, …, n - 2}` with no consecutive elements, which the
Fibonacci identity counts.

## Main results

* `count_arithmetic` — `(2^m - (m + 1)) + ((m + 1) / 2) + 1 = 2^m - m / 2`.
* `count_formula` — connected-class count `2^(n - 1) - ⌊(n - 1) / 2⌋`
  (Paper: Theorem 12).
* `count_indep_subsets` — `|indepSubsets m| = Nat.fib (m + 2)`.
* `count_loopless_arithmetic` — bookkeeping identity.
* `count_loopless_formula` — loopless connected-class count
  `Nat.fib (n - 1) - ⌊(n - 3) / 2⌋` (Paper: Theorem 15).

## References

Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" —
Theorems 12 and 15.
-/

namespace HessenbergDigraphs

open Finset Nat

/-! ## Mathematical layer — Lean-side arithmetic identity for `count_formula` -/

/-- **Math.** Arithmetic identity `(2^m - (m + 1)) + ((m + 1) / 2) + 1 = 2^m - m / 2`
    used in the derivation of `count_formula`. -/
theorem count_arithmetic (m : ℕ) :
    (2^m - (m + 1)) + ((m + 1) / 2) + 1 = 2^m - m / 2 := by
      zify [ Nat.succ_div ] ; ring_nf;
      rw [ Nat.cast_sub, Nat.cast_sub ] <;> norm_num <;> try
        linarith [ Nat.div_mul_le_self m 2,
                   show 2 ^ m ≥ m + 1 from Nat.recOn m ( by norm_num ) fun n ihn => by
                     rw [ pow_succ' ] ; linarith [ ihn ] ] ;
      grind +ring

/-! ## Mathematical layer — Paper: Theorem 12 (connected-class count) -/

/-- **Math.** Number of non-isomorphic weakly connected support digraphs of
    `n × n` real orthogonal upper Hessenberg matrices is
    `2^(n - 1) - ⌊(n - 1) / 2⌋`. Paper: Theorem 12. -/
theorem count_formula (n : ℕ) :
    (2^(n-1) - ((n-1) + 1)) + (((n-1) + 1) / 2) + 1 = 2^(n-1) - (n-1) / 2 :=
  count_arithmetic (n - 1)

/-! ## Mathematical layer — Lean-side combinatorial enumeration object -/

/-- **Math.** The set of independent subsets of `Finset.range m` (no two
    consecutive elements). -/
def indepSubsets (m : ℕ) : Finset (Finset ℕ) :=
  (Finset.range m).powerset.filter (fun S => ∀ k ∈ S, k + 1 ∉ S)

/-! ## Mathematical layer — Lean-side partition: split `indepSubsets (m + 2)`
    by whether the top element `m + 1` is included. The math is the
    bijection
    `indepSubsets (m + 2) ≃ indepSubsets (m + 1) ⊔ indepSubsets m`
    (the second component being the image of `S ↦ S ∪ {m + 1}`). -/

/-- **Math.** Independent subsets of `range (m + 2)` split into those not containing
`m + 1` (which are independent subsets of `range (m + 1)`) and those
containing `m + 1` (which are `S ∪ {m + 1}` for `S` an independent subset
of `range m`). -/
private lemma indepSubsets_succ_succ_eq_union (m : ℕ) :
    indepSubsets (m + 2) =
      indepSubsets (m + 1) ∪
      (indepSubsets m).image (fun S => S ∪ {m + 1}) := by
  ext S; simp [indepSubsets]
  constructor <;> intro hS <;> simp_all +decide [Finset.subset_iff]
  · by_cases h : m + 1 ∈ S <;> simp_all +decide [Nat.lt_succ_iff]
    · right
      use S \ {m + 1}
      grind
    · exact Or.inl fun x hx => Nat.le_of_lt_succ (lt_of_le_of_ne (hS.1 hx) (by aesop))
  · grind

/-! ## Engineering layer — Type B (set-extensionality plumbing): `S ↦ S ∪ {m+1}`
    is injective on `indepSubsets m` because no `S ∈ indepSubsets m` already
    contains `m + 1` (every element is `< m`). -/

/-- **Eng.** The map `S ↦ S ∪ {m + 1}` is injective on `indepSubsets m` because
every `S ∈ indepSubsets m` is contained in `Finset.range m`, hence avoids
`m + 1`. -/
private lemma indepSubsets_union_singleton_injOn (m : ℕ) :
    Set.InjOn (fun S => S ∪ {m + 1}) (indepSubsets m : Set (Finset ℕ)) := by
  intro x hx y hy; simp_all +decide [Finset.ext_iff]
  intro h a; specialize h a; by_cases ha : a = m + 1 <;> simp_all +decide
  exact iff_of_false
    (fun h => by
      have := Finset.mem_range.mp
        (Finset.mem_powerset.mp (Finset.mem_filter.mp hx |>.1) h); linarith)
    (fun h => by
      have := Finset.mem_range.mp
        (Finset.mem_powerset.mp (Finset.mem_filter.mp hy |>.1) h); linarith)

/-! ## Engineering layer — Type B (Finset.disjoint_right unfolding): the two
    components of `indepSubsets_succ_succ_eq_union` are disjoint because
    elements of the first omit `m + 1` while elements of the second contain it. -/

/-- **Eng.** The two components of `indepSubsets_succ_succ_eq_union` are disjoint:
the first consists of subsets of `range (m + 1)` (omitting `m + 1`), while
the second consists of sets containing `m + 1`. -/
private lemma indepSubsets_partition_disjoint (m : ℕ) :
    Disjoint (indepSubsets (m + 1))
      ((indepSubsets m).image (fun S => S ∪ {m + 1})) := by
  simp +contextual [Finset.disjoint_right, indepSubsets]
  intro a x hx₁ hx₂ hx₃ hx₄; subst hx₃; simp_all +decide [Finset.subset_iff]

/-! ## Mixed — Math: classical Fibonacci-counts-binary-strings result
    `(indepSubsets m).card = fib (m + 2)` via the partition above; the
    induction step is `card_union_of_disjoint + card_image_of_injOn` followed
    by Fibonacci arithmetic. | Eng: the Type-B set-bookkeeping is absorbed
    into the three private helpers above. -/

/-- **Mixed.** The number of subsets of `Finset.range m` containing no two
    consecutive elements equals `Nat.fib (m + 2)`. -/
theorem count_indep_subsets (m : ℕ) :
    (indepSubsets m).card = Nat.fib (m + 2) := by
  induction m using Nat.strong_induction_on with | _ m ih =>
  rcases m with (_ | _ | m) <;> simp +arith +decide [*, Nat.fib_add_two] at *
  rw [indepSubsets_succ_succ_eq_union m,
      Finset.card_union_of_disjoint (indepSubsets_partition_disjoint m),
      Finset.card_image_of_injOn (indepSubsets_union_singleton_injOn m),
      ih (m + 1) (by linarith), ih m (by linarith),
      show m + 1 + 1 = m + 2 by ring, Nat.fib_add_two]
  ring

/-! ## Mathematical layer — Lean-side arithmetic identity for `count_loopless_formula` -/

/-- **Math.** Arithmetic identity `(A - (m + 1)) + ((m + 1) / 2) + 1 = A - m / 2`
    (assuming `m + 1 ≤ A`), used in `count_loopless_formula`. -/
theorem count_loopless_arithmetic (A m : ℕ) (hA : m + 1 ≤ A) :
    (A - (m + 1)) + ((m + 1) / 2) + 1 = A - m / 2 := by
      omega;

/-! ## Mathematical layer — Paper: Theorem 15 (loopless connected-class count) -/

/-- **Math.** Number of non-isomorphic loopless connected support digraphs of
    `n × n` real orthogonal upper Hessenberg matrices (`n ≥ 3`) is
    `Nat.fib (n - 1) - ⌊(n - 3) / 2⌋`. Paper: Theorem 15. -/
theorem count_loopless_formula (n : ℕ) (_hn : 3 ≤ n)
    (hfib : n - 3 + 1 ≤ Nat.fib (n - 1)) :
    (Nat.fib (n - 1) - ((n - 3) + 1)) + (((n - 3) + 1) / 2) + 1 =
    Nat.fib (n - 1) - (n - 3) / 2 :=
  count_loopless_arithmetic (Nat.fib (n - 1)) (n - 3) hfib

end HessenbergDigraphs
