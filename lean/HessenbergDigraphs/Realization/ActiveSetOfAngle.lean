/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Util.Linter.MathTag
import Mathlib.Analysis.Complex.Trigonometric
import HessenbergDigraphs.ActiveSet
import HessenbergDigraphs.Vertex

/-!
# Active set extracted from a Givens parameter (bundled-structure form)
-/

namespace HessenbergDigraphs

open Matrix Finset

/-- **Math.** The active set of angles, returned as an `ActiveSet n` whose elements
are the `Vertex (n - 1)` indices `k + 1` for which `cos θ_k ≠ 0`. -/
noncomputable def activeSet {n : ℕ} (θ : Fin (n - 1) → ℝ) : ActiveSet n where
  elements :=
    (Finset.univ.filter (fun k : Fin (n - 1) => Real.cos (θ k) ≠ 0)).image
      (fun k : Fin (n - 1) =>
        ({ value := k.val + 1
           one_le_value := Nat.succ_le_succ (Nat.zero_le _)
           value_le_n := by have := k.isLt; omega } : Vertex (n - 1)))

end HessenbergDigraphs
