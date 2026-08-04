/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!
# Vertex: 1-indexed vertices of `D_n`

A `Vertex n` is a vertex label `v` with `1 ≤ v ≤ n` — the natural domain
in which the paper "Digraphs of Real Orthogonal Upper Hessenberg Matrices"
states all combinatorial facts (vertex 1, vertex 2, …, vertex n).

The Lean side has historically used `Fin n` (0-indexed) for matrix
indexing and explicit `(i.val + 1) ∈ activeRows S`-style translations
to bridge to the paper's 1-indexed convention. This file introduces
`Vertex n` as the paper-aligned type, with a Type-B-tax-free API for
construction, comparison, neighbouring, and round-trip with `Fin n`.

## Main definitions

* `Vertex n` — structure carrying `value : ℕ` together with `1 ≤ value ≤ n`.
* `Vertex.toFin`, `Vertex.ofFin` — round-trip with `Fin n`.
* `Vertex.first`, `Vertex.last` — endpoints (require `1 ≤ n`).
* `Vertex.next`, `Vertex.previous` — partial successor / predecessor with
  explicit precondition (matches the project-wide pattern in
  `Combinatorial.Arc` and `Realization.*`).

## Implementation notes

* The `value` field is paper-1-indexed; to use a `Vertex n` to index a
  `Matrix (Fin n) (Fin n) ℝ`, take `Vertex.toFin`.
* No `Coe (Vertex n) ℕ` is provided — use `.value` explicitly to keep
  `Arc S i j` (taking `Vertex n` arguments) call sites unambiguous.
* `next` / `previous` take an explicit hypothesis, matching the project-wide
  convention of `(hv : 1 ≤ v)` / `(hv : 2 ≤ v)` style preconditions.
  An `Option`-valued alternative would force `Option.get` plumbing at
  every call site, conflicting with this style.

## References

Severini, "Digraphs of Real Orthogonal Upper Hessenberg Matrices" — §0
(vertex set notation `[n] = {1, …, n}`).
-/

namespace HessenbergDigraphs

/-! ## Mathematical layer — paper-side vertex type. A `Vertex n` is a label
    `v ∈ {1, …, n}` (Severini §0). The fields `one_le_value` and `value_le_n` carry
    the bound proofs; the body is plain `ℕ`. -/

/-- **Math.** A vertex of the digraph `D_n`: a natural number `value` with
`1 ≤ value ≤ n` (paper-side 1-indexed). -/
@[ext]
structure Vertex (n : ℕ) where
  value : ℕ
  one_le_value : 1 ≤ value
  value_le_n : value ≤ n
  deriving DecidableEq

namespace Vertex

variable {n : ℕ}

section RoundTrip

/-! ## Engineering layer — Type B bridge: `Vertex n ↔ Fin n` (paper
    1-indexed ↔ Lean 0-indexed). `toFin` shifts down by one; `ofFin`
    shifts up by one. -/

/-- **Eng.** Convert a 1-indexed vertex to its 0-indexed `Fin n` counterpart by
subtracting one. -/
def toFin (v : Vertex n) : Fin n :=
  ⟨v.value - 1, by have := v.one_le_value; have := v.value_le_n; omega⟩

/-- **Eng.** Convert a 0-indexed `Fin n` to its 1-indexed vertex counterpart by
adding one. -/
def ofFin (i : Fin n) : Vertex n where
  value := i.val + 1
  one_le_value := Nat.succ_le_succ (Nat.zero_le _)
  value_le_n := by have := i.isLt; omega

/-! ## Mathematical layer — round-trip identities for `Vertex ↔ Fin`. -/

/-- **Math.** `ofFin` is the right inverse of `toFin`. -/
@[simp] theorem toFin_ofFin (i : Fin n) : (ofFin i).toFin = i := by
  ext; simp [toFin, ofFin]

/-- **Math.** `ofFin` is the left inverse of `toFin`. -/
@[simp] theorem ofFin_toFin (v : Vertex n) : ofFin v.toFin = v := by
  ext
  change v.value - 1 + 1 = v.value
  have := v.one_le_value
  omega

end RoundTrip

section Endpoints

/-! ## Mathematical layer — endpoint vertices `1` and `n`, valid whenever
    `1 ≤ n`. -/

/-- **Math.** The first vertex `1`. Requires `1 ≤ n`. -/
def first (h : 1 ≤ n) : Vertex n where
  value := 1
  one_le_value := le_refl _
  value_le_n := h

/-- **Math.** The last vertex `n`. Requires `1 ≤ n`. -/
def last (h : 1 ≤ n) : Vertex n where
  value := n
  one_le_value := h
  value_le_n := le_refl _

end Endpoints

section SuccPred

/-! ## Engineering layer — Type C tool: partial `next` / `previous` with
    explicit precondition. Matches the project-wide style of explicit
    `(hv : 1 ≤ v)` / `(hv : 2 ≤ v)` preconditions over `Option`-valued
    alternatives, which would force `Option.get` plumbing at every
    call site. -/

/-- **Eng.** The next vertex `v + 1`. Requires `v.value < n` (i.e. `v` is not the
last vertex). -/
def next (v : Vertex n) (h : v.value < n) : Vertex n where
  value := v.value + 1
  one_le_value := by have := v.one_le_value; omega
  value_le_n := h

/-- **Eng.** The previous vertex `v - 1`. Requires `2 ≤ v.value` (i.e. `v` is not
the first vertex). -/
def previous (v : Vertex n) (h : 2 ≤ v.value) : Vertex n where
  value := v.value - 1
  one_le_value := by omega
  value_le_n := by have := v.value_le_n; omega

/-- **Math.** The `value` of `v.next h` is `v.value + 1`. -/
@[simp] theorem next_value (v : Vertex n) (h : v.value < n) :
    (v.next h).value = v.value + 1 := rfl

/-- **Math.** The `value` of `v.previous h` is `v.value - 1`. -/
@[simp] theorem previous_value (v : Vertex n) (h : 2 ≤ v.value) :
    (v.previous h).value = v.value - 1 := rfl

end SuccPred

section Comparison

/-! ## Engineering layer — `Vertex n` inherits its order from `ℕ` through
    the `value` field, via `LinearOrder.lift' Vertex.value`. One instance
    delivers `≤`, `<`, `min`, `max`, `Finset.max'` / `sort`, decidable
    comparison, and every order lemma at once, with `v ≤ w` definitionally
    `v.value ≤ w.value`. The `le_iff` / `lt_iff` simp lemmas pin that
    `.value` normal form, which is how the rest of the development reasons
    about vertex order. -/

instance : LinearOrder (Vertex n) :=
  LinearOrder.lift' Vertex.value (fun _ _ h => Vertex.ext h)

@[simp] theorem le_iff (v w : Vertex n) : v ≤ w ↔ v.value ≤ w.value := Iff.rfl
@[simp] theorem lt_iff (v w : Vertex n) : v < w ↔ v.value < w.value := Iff.rfl

end Comparison

section Casts

/-! ## Engineering layer — Type B helper: cast a vertex from a smaller
    bound to a larger one (`castGE`). Used downstream by
    `HessenbergDigraphs.ActiveSet` to lift vertices of `Vertex (n - 1)`
    (active-set elements) to `Vertex n` (active-column elements). -/

/-- **Eng.** Cast a vertex from `Vertex n` to `Vertex m` when `n ≤ m`. The value is
preserved; the upper bound `value ≤ m` follows from `value ≤ n ≤ m`. -/
def castGE {n m : ℕ} (h : n ≤ m) (v : Vertex n) : Vertex m where
  value := v.value
  one_le_value := v.one_le_value
  value_le_n := le_trans v.value_le_n h

@[simp] theorem castGE_value {n m : ℕ} (h : n ≤ m) (v : Vertex n) :
    (castGE h v).value = v.value := rfl

/-! ## Engineering layer — Type B helper: lift `i : Fin (n - 1)` to
    `Vertex n` with value `i.val + 1`. This is `Vertex.ofFin`
    (`Fin (n-1) → Vertex (n-1)`, the `+1` is already here) followed by
    the value-preserving `Vertex.castGE` inclusion `Vertex (n-1) ↪ Vertex n`.
    Used in cardinality arguments where the active set ranges over
    `Vertex (n - 1)` but the surrounding statement is in `Vertex n`. -/

/-- **Eng.** Lift `i : Fin (n - 1)` to a `Vertex n` whose value is `i.val + 1`,
as `castGE (ofFin i)`. -/
def ofFinSucc {n : ℕ} (i : Fin (n - 1)) : Vertex n :=
  castGE (Nat.sub_le n 1) (ofFin i)

@[simp] theorem ofFinSucc_value {n : ℕ} (i : Fin (n - 1)) :
    (ofFinSucc i : Vertex n).value = i.val + 1 := rfl

/-! ## Engineering layer — Type C helper: subtract `k` from `v.value`
    along the spine (iterated `previous`). Required precondition
    `k < v.value` keeps the result in `[1, n]`. Used in the spine-arc
    descent of `singleton_iso_unique`. Pure ℕ-subtraction semantics —
    no paper-specific naming, just "vertex with value `v.value - k`". -/

/-- **Eng.** The vertex with value `v.value - k`. Requires `k < v.value`. -/
def subtract {n : ℕ} (v : Vertex n) (k : ℕ) (h : k < v.value) : Vertex n where
  value := v.value - k
  one_le_value := by have := v.one_le_value; omega
  value_le_n := by have := v.value_le_n; omega

@[simp] theorem subtract_value {n : ℕ} (v : Vertex n) (k : ℕ) (h : k < v.value) :
    (v.subtract k h).value = v.value - k := rfl

@[simp] theorem subtract_zero {n : ℕ} (v : Vertex n) (h : 0 < v.value) :
    v.subtract 0 h = v := by ext; change v.value - 0 = v.value; omega

end Casts

section Finiteness

/-! ## Engineering layer — `Fintype (Vertex n)` instance via the
    `Vertex n ≃ Fin n` round-trip (toFin / ofFin). Required to use
    `Finset.univ : Finset (Vertex n)` for enumeration in degree
    arguments etc. -/

/-- **Eng.** `Vertex n` is finite, in bijection with `Fin n` via `toFin / ofFin`. -/
instance instFintype : Fintype (Vertex n) :=
  Fintype.ofEquiv (Fin n)
    { toFun := ofFin
      invFun := toFin
      left_inv := toFin_ofFin
      right_inv := ofFin_toFin }

/-- **Math.** `Vertex n` has exactly `n` elements: `|{1, …, n}| = n`. -/
@[simp] theorem card_eq (n : ℕ) : Fintype.card (Vertex n) = n := by
  rw [Fintype.card_congr (⟨toFin, ofFin, ofFin_toFin, toFin_ofFin⟩ : Vertex n ≃ Fin n),
    Fintype.card_fin]

end Finiteness

end Vertex

end HessenbergDigraphs
