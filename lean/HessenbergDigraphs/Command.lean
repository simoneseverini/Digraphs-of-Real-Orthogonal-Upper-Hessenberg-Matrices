/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Xinze Li, Simone Severini
-/
import HessenbergDigraphs.Render

/-!
# Syntax layer — user-facing `#hessenberg` commands

Multiple syntactic forms sharing a single rendering pipeline:
`propsFromVerified` computes the payload through the verified `Compute`
layer (so the rendered digraph is the formal `Arc`/`Loop`/`outDeg`
objects evaluated), then ships it to the `HessenbergGraph` widget.

## Commands

* `#hessenberg n {k₁, k₂, …}` — full profile of `D_n(S)`:
  digraph, support matrix, degrees, properties, certificates.
* `#hessenberg_count n` — classification counts for dimension `n`.
-/

namespace HessenbergDigraphs

/-- **Eng.** Build an `ActiveSet n` from a raw list of paper-side values,
discharging the `1 ≤ k ≤ n - 1` bound in place via a dependent `if`.
Out-of-range values are dropped (the command warns on them separately). -/
private def activeSetOfNats (n : Nat) (elems : List Nat) : ActiveSet n :=
  ⟨(elems.filterMap fun k =>
      if h : 1 ≤ k ∧ k ≤ n - 1 then
        some (⟨k, h.1, h.2⟩ : Vertex (n - 1))
      else none).toFinset⟩

/-- **Eng.** Widget props for `D_n(S)`, computed through the verified
`Compute` layer. Arcs and loops come from `decide (Arc S · ·)` on the
formal arc relation; degrees from the formal `outDeg`/`inDeg`; the active
row/column sets from `S.activeRows`/`S.activeCols`. Every rendered edge is
thus the formal object evaluated, not a parallel re-implementation — so the
cited theorems certify exactly what is drawn. -/
private def propsFromVerified (n : Nat) (elems : List Nat) :
    HessenbergGraphProps :=
  let S : ActiveSet n := activeSetOfNats n elems
  let loopless := S.isLoopless
  let degrees := S.degreeList.map fun (v, od, id) =>
    ({ vertex := v, outDeg := od, inDeg := id } : DegreeEntry)
  let totalCls := countClasses n
  let looplessCls := countLooplessClasses n
  let sortVals (t : Finset ℕ) : List ℕ := t.sort (· ≤ ·)
  let certs : List CertEntry := [
    { thmName := "mem_arcList_iff_digraph"
      claim := "arc list = D_n(S), sound & complete" },
    { thmName := "hcycle_subset"
      claim := "Hamilton cycle contained" }
  ] ++ (if loopless then
    [{ thmName := "isLoopless_iff"
       claim := "isLoopless ⇔ no self-loop" }]
  else
    [{ thmName := "mem_loopVertices_iff"
       claim := "loop list = self-loop vertices" }])
  ++ [
    { thmName := "mem_degreeList_iff"
      claim := "degrees = formal outDeg/inDeg" },
    { thmName := "outDeg_first"
      claim := "outDeg(v1) = |S| + 1" },
    { thmName := "inDeg_last"
      claim := "inDeg(v" ++ toString n ++ ") = |S| + 1" },
    { thmName := "rigid"
      claim := "S unique from D_n(S) for |S| ≥ 2" },
    { thmName := "completeness"
      claim := "S realizable by some θ ∈ Θ_n" },
    { thmName := "digraph_model"
      claim := "support(Q_n(θ)) = D_n(S(θ))" },
    { thmName := "countClasses_eq_card_isoClasses"
      claim := toString totalCls ++ " iso classes (verified = #classes) n=" ++
        toString n },
    { thmName := "countLooplessClasses_eq_card_looplessClasses"
      claim := toString looplessCls ++ " loopless classes (verified) n=" ++
        toString n }
  ]
  { n := n
    activeSet := (sortVals S.values).toArray
    activeRows := (sortVals (S.activeRows.image Vertex.value)).toArray
    activeCols := (sortVals (S.activeCols.image Vertex.value)).toArray
    arcs := S.arcList.toArray
    spineArcs := S.spineArcList.toArray
    overlayArcs := S.overlayArcList.toArray
    loops := S.loopVertices.toArray
    degrees := degrees.toArray
    isLoopless := loopless
    totalClasses := totalCls
    looplessClasses := looplessCls
    certificates := certs.toArray }

open Lean Elab Command ProofWidgets in
/-- **Eng.** `#hessenberg n {k₁, k₂, …}` — interactive widget with
digraph, matrix pattern, and theorem certificates. -/
scoped syntax "#hessenberg " num " {" num,* "}" : command

open Lean Elab Command ProofWidgets in
scoped elab_rules : command
  | `(command| #hessenberg%$tk $nStx:num { $[$elStx:num],* }) => do
    let n := nStx.getNat
    let elems := elStx.toList.map (·.getNat)
    if n < 2 then
      logWarning m!"n must be ≥ 2"
      return
    for e in elems do
      if e < 1 || e > n - 1 then
        logWarning m!"element {e} out of range [1, {n - 1}]"
        return
    let props := propsFromVerified n elems
    liftCoreM <| Lean.Widget.savePanelWidgetInfo
      (hash HessenbergGraph.javascript)
      (Lean.Server.RpcEncodable.rpcEncode props)
      tk

open Lean Elab Command ProofWidgets in
/-- **Eng.** `#hessenberg_count n` — classification counts with
certificates. Uses empty active set widget with count-only data. -/
scoped syntax "#hessenberg_count " num : command

open Lean Elab Command ProofWidgets in
scoped elab_rules : command
  | `(command| #hessenberg_count%$tk $nStx:num) => do
    let n := nStx.getNat
    let totalCls := countClasses n
    let looplessCls := countLooplessClasses n
    let certs : List CertEntry := [
      { thmName := "countClasses_eq_card_isoClasses"
        claim := toString totalCls ++ " iso classes (verified = #classes)" ++
          " = 2^" ++ toString (n-1) ++ " - " ++ toString ((n-1)/2) },
      { thmName := "countLooplessClasses_eq_card_looplessClasses"
        claim := toString looplessCls ++ " loopless classes (verified = #classes)" ++
          " = Fib(" ++ toString (n-1) ++ ") - " ++ toString ((n-3)/2) },
      { thmName := "count_indep_subsets"
        claim := "loopless sets counted by Fibonacci" }
    ]
    let props : HessenbergGraphProps := {
      n := n
      activeSet := #[]
      activeRows := #[]
      activeCols := #[]
      arcs := #[]
      spineArcs := #[]
      overlayArcs := #[]
      loops := #[]
      degrees := #[]
      isLoopless := true
      totalClasses := totalCls
      looplessClasses := looplessCls
      certificates := certs.toArray }
    liftCoreM <| Lean.Widget.savePanelWidgetInfo
      (hash HessenbergGraph.javascript)
      (Lean.Server.RpcEncodable.rpcEncode props)
      tk

end HessenbergDigraphs
