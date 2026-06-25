/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import Lean
import ProofWidgets.Component.Basic
import HessenbergDigraphs.Compute.Query

/-!
# Rendering API — widget props and component

Defines the data contract between the command layer and the JS
renderer. The command layer populates `HessenbergGraphProps`; the
renderer (`widget/hessenbergDigraph.js`) consumes it.

## Main definitions

* `CertEntry` — one theorem certificate (`thmName` + `claim`).
* `DegreeEntry` — per-vertex degree data.
* `HessenbergGraphProps` — full rendering payload.
* `HessenbergGraph` — the `@[widget_module]` component.
-/

namespace HessenbergDigraphs

open Lean ProofWidgets

structure CertEntry where
  thmName : String
  claim : String
  deriving ToJson, FromJson, Inhabited

structure DegreeEntry where
  vertex : Nat
  outDeg : Nat
  inDeg : Nat
  deriving ToJson, FromJson, Inhabited

structure HessenbergGraphProps where
  n : Nat
  activeSet : Array Nat
  activeRows : Array Nat
  activeCols : Array Nat
  arcs : Array (Nat × Nat)
  spineArcs : Array (Nat × Nat)
  overlayArcs : Array (Nat × Nat)
  loops : Array Nat
  degrees : Array DegreeEntry
  isLoopless : Bool
  totalClasses : Nat
  looplessClasses : Nat
  certificates : Array CertEntry
  deriving ToJson, FromJson, Inhabited, Server.RpcEncodable

@[widget_module]
def HessenbergGraph : Component HessenbergGraphProps where
  javascript := include_str ".." / "widget" / "hessenbergDigraph.js"


end HessenbergDigraphs
