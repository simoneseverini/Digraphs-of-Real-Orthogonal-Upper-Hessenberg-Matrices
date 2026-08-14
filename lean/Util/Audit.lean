/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import Lean

/-!
# `lake exe hessenberg-audit`

One-command health check for the `HessenbergDigraphs` library. Performs:

1. **Public-API listing.** Prints the canonical paper-facing definitions
   and theorems and confirms each one is present in the imported
   environment. A missing declaration is a hard failure.
2. **Foundational-axiom audit.** Walks the proof terms of the apex
   public theorems via `Environment.find?` + `Expr.foldConsts`,
   transitively collecting every `axiomInfo` reachable from the proof.
   Confirms that the only foundational axioms reached are
   `propext`, `Classical.choice`, and `Quot.sound`. Any other axiom
   (notably `sorryAx`) causes a non-zero exit.

The exit code is `0` on success and `1` on any audit failure.
Intended for both interactive use (developer one-shot check) and
CI invocation.

This file deliberately avoids importing `HessenbergDigraphsMatrix`
statically: that would force the audit executable to link the entire
transitive Mathlib closure, which exceeds macOS's `ARG_MAX` linker
argument limit. Instead, target names are constructed as `Name`
literals and the library is loaded at runtime via `importModules`.
-/

open Lean

/-- Build a `Name` of the form `HessenbergDigraphs.<s>` without needing
the corresponding constant in scope (which would force a static import
of the audited module). -/
private def hd (s : String) : Name :=
  .str (.str .anonymous "HessenbergDigraphs") s

/-- Foundational axioms expected for every public theorem. The three
core Lean axioms `propext`, `Classical.choice`, `Quot.sound` are in
scope via `import Lean`, so the `` `` `` quoting form is fine here. -/
private def expectedAxioms : NameSet :=
  NameSet.empty
    |>.insert ``propext
    |>.insert ``Classical.choice
    |>.insert ``Quot.sound

/-- Walk the environment from `name`, accumulating every constant of
kind `axiomInfo` reachable through `value?` references. -/
private partial def collectAxiomDeps (env : Environment)
    (name : Name) (visited : NameSet := {}) (acc : NameSet := {}) :
    NameSet × NameSet :=
  if visited.contains name then
    (visited, acc)
  else
    let visited := visited.insert name
    match env.find? name with
    | none => (visited, acc)
    | some (.axiomInfo _) => (visited, acc.insert name)
    | some info =>
      let body := info.value?.getD (.const name [])
      body.foldConsts (init := (visited, acc))
        fun n (v, a) => collectAxiomDeps env n v a

/-- Audit one named theorem. Returns `true` on success. -/
private def auditTheorem (env : Environment) (thm : Name) : IO Bool := do
  let (_, axs) := collectAxiomDeps env thm
  let unexpected := axs.toList.filter (fun a => !expectedAxioms.contains a)
  if unexpected.isEmpty then
    IO.println s!"  ✓ {thm}"
    return true
  else
    IO.println s!"  ✗ {thm} — unexpected axioms: {unexpected}"
    return false

/-- Build a `Name` of the form `Matrix.<s>` for declarations in the
extracted Mathlib-style Givens / sign-equivalence / Hessenberg modules. -/
private def mx (s : String) : Name :=
  .str (.str .anonymous "Matrix") s

/-- Build `Matrix.SignEquiv.<s>` (used for the dot-notation API). -/
private def mxse (s : String) : Name :=
  .str (.str (.str .anonymous "Matrix") "SignEquiv") s

/-- Public definitions: paper-facing types and constructions. -/
private def publicDefs : List (Name × String) :=
  [ (hd "Arc",                "def        (support digraph arcs, Definition 6)")
  , (mx "IsUpperHessenberg",  "def        (upper Hessenberg predicate)")
  , (mx "IsUnreduced",        "def        (unreduced predicate)")
  , (mx "SignEquiv",          "def        (sign-equivalence relation)")
  , (mx "givensRotation",     "def        (Givens rotation factor)")
  , (mx "givensProduct",      "def        (canonical Givens product)")
  , (hd "activeSet",          "def        (active set extraction θ ↦ S)") ]

/-- Apex public theorems audited for axiom purity. -/
private def publicTheorems : List (Name × String) :=
  [ (hd "classification",
       "theorem    (apex: support digraphs ↔ {D_n(S)}, sec-introduction)")
  , (hd "completeness",
       "theorem    (realizability: every valid S = activeSet θ for some unreduced θ)")
  , (hd "digraph_model",
       "theorem    (bridge: Givens product → combinatorial model)")
  , (mx "givensProduct_apply_of_break",
       "theorem    (connectivity: subdiagonal break → block-diagonal)")
  , (mxse "preserves_support",
       "theorem    (support is sign-equivalence invariant)")
  , (mx "givensProduct_isUpperHessenberg",
       "theorem    (Givens products are upper Hessenberg)")
  , (hd "rigid",
       "theorem    (automorphism rigidity for |S| ≥ 2, Theorem 10)")
  , (hd "singleton_iso",
       "theorem    (singleton isomorphism {t} ↔ {n-t}, Lemma 11)")
  , (hd "singleton_iso_unique",
       "theorem    (uniqueness of singleton isomorphism)")
  , (hd "loopless_iff",
       "theorem    (loopless characterization, Corollary 14)")
  , (hd "count_formula",
       "theorem    (enumeration: 2^(n-1) − ⌊(n-1)/2⌋, Theorem 12)")
  , (hd "card_isoClasses",
       "theorem    (class count as a cardinality: #iso classes = 2^(n-1) − ⌊(n-1)/2⌋)")
  , (hd "card_isoClasses_quot",
       "theorem    (readable count: Nat.card of the iso-class quotient = 2^(n-1) − ⌊(n-1)/2⌋)")
  , (hd "realizable_classCount",
       "theorem    (calculator ↔ Givens-product supports = {D_n(S)}, counted by countClasses)")
  , (hd "matrix_classCount",
       "theorem    (calculator ↔ unreduced O.H. matrix supports = {D_n(S)}, counted by countClasses)")
  , (hd "count_loopless_formula",
       "theorem    (loopless enumeration: fib(n-1) − ⌊(n-3)/2⌋, Theorem 15)")
  , (hd "card_looplessClasses",
       "theorem    (loopless class count as a cardinality: #loopless classes = fib(n-1) − ⌊(n-3)/2⌋)")
  , (hd "card_looplessClasses_quot",
       "theorem    (readable loopless count: Nat.card of the loopless quotient = fib(n-1) − ⌊(n-3)/2⌋)")
  , (.str (.str (.str .anonymous "HessenbergDigraphs") "OrthogonalHessenberg")
       "exists_givensFactorization",
       "theorem    (universality: every unreduced O.H. matrix is sign-equivalent to a Givens product)") ]

def main : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules
    #[(`HessenbergDigraphs : Import)] {} (trustLevel := 0)

  IO.println "HessenbergDigraphs library audit"
  IO.println "================================"
  IO.println ""

  let mut allOk := true

  IO.println "Public definitions:"
  for (n, kind) in publicDefs do
    if env.contains n then
      IO.println s!"  • {n}\n      {kind}"
    else
      IO.println s!"  ✗ {n} — NOT FOUND in environment"
      allOk := false
  IO.println ""

  IO.println "Public theorems:"
  for (n, kind) in publicTheorems do
    if env.contains n then
      IO.println s!"  • {n}\n      {kind}"
    else
      IO.println s!"  ✗ {n} — NOT FOUND in environment"
      allOk := false
  IO.println ""

  IO.println "Foundational-axiom audit:"
  for (thm, _) in publicTheorems do
    if env.contains thm then
      let ok ← auditTheorem env thm
      if !ok then allOk := false
  IO.println ""

  if allOk then
    IO.println "All apex public theorems depend only on:"
    IO.println "  propext, Classical.choice, Quot.sound"
    IO.println ""
    IO.println "Library status: ✓ healthy"
    return 0
  else
    IO.println "Library status: ✗ audit FAILED"
    return 1
