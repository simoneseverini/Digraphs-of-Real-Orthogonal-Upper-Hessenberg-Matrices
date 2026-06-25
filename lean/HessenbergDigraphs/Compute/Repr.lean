/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import HessenbergDigraphs.ActiveSet
import Mathlib.Data.Finset.Sort

/-!
# Display instances for core types

`Repr` and `ToString` instances for `Vertex` and `ActiveSet`, enabling
`#eval` output in the Infoview.

## Main definitions

* `Repr (Vertex n)` — displays as `v3`.
* `ToString (Vertex n)` — displays as `3`.
* `Repr (ActiveSet n)` — displays as `{2, 4}`.
* `ToString (ActiveSet n)` — displays as `{2, 4}`.
-/

namespace HessenbergDigraphs

instance : Repr (Vertex n) where
  reprPrec v _ := s!"v{v.value}"

instance : ToString (Vertex n) where
  toString v := s!"{v.value}"

instance : Repr (ActiveSet n) where
  reprPrec S _ :=
    let vals := S.values.sort (· ≤ ·)
    "{" ++ ", ".intercalate (vals.map toString) ++ "}"

instance : ToString (ActiveSet n) where
  toString S :=
    let vals := S.values.sort (· ≤ ·)
    "{" ++ ", ".intercalate (vals.map toString) ++ "}"

end HessenbergDigraphs
