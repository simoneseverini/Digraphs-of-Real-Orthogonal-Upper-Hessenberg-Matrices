/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import Lean

/-!
# `lake exe hessenberg-compression`

Compute Aksenov-style compression metrics for the `HessenbergDigraphs`
public declarations, following Aksenov, Bodnia, Freedman, and Mulligan,
"Compression is all you need: Modeling Mathematics"
(arXiv:2603.20396, 2026), §3.1–§3.2.

For each target declaration we report:

* **wrapped length** — number of tokens in the declaration's source,
  per Aksenov §3.2 ("tokens in its definition written in Lean as
  produced by the Lean parser"). Computed by locating the declaration's
  `.lean` source via its `DeclarationRange`, then running a hand-rolled
  lexer (`lexTokenCount`) over the source slice. The lexer skips
  whitespace, line comments, and nested block comments; counts each
  maximal run of identifier characters as one token; counts each ASCII
  operator/punctuation character and each Unicode character (`→`, `≤`,
  `θ`, `ℕ`, …) as one token. This is an approximation of Lean's actual
  surface lexer — `runParserCategory` would be more faithful but does
  not survive on isolated source slices that lack the surrounding
  module's `open`/`namespace` parser state. When the source cannot
  be located (e.g. Mathlib-side declarations not co-located with the
  executable), we fall back to a `Lean.Expr`-node count of the
  elaborated body, marked `*` in output.
* **unwrapped length** — total count of primitives reachable when
  every constant reference is recursively expanded down to primitives.
  Computed exactly per Aksenov §3.2:
    `|u|_G = Σᵢ wᵢ · |vᵢ|_G`     for non-primitive `u` with edges to
                                  `v₁, …, vₖ` of weights `w₁, …, wₖ`;
    `|u|_G = 1`                  for primitives.
* **depth** — longest path in the dependency DAG from `u` to a
  primitive. Primitives have depth 0; otherwise `depth(u) = 1 +
  max_i depth(vᵢ)`.

## Definition of "primitive"

Aksenov §3.2 specifies primitives as "Lean core library elements and
`Sort`". We classify a `ConstantInfo` as primitive iff the module in
which it was declared has a name starting with `Init` or `Lean`
(matching Lean's core toolchain libraries). `Sort` itself is not a
`ConstantInfo` — it appears in expressions as the `Expr.sort _`
constructor — so we inject it into the dependency graph via a
sentinel name `_aksenov_sort_primitive` whose metrics are hard-coded
to `(1, 1, 0)`, exactly as Aksenov's §3.1 `collectElems` treats it.
User-defined inductive types, constructors, recursors, and opaque
declarations are **non-primitive**: we extract their structural
references from the declaration's `type` rather than its `value?`,
since `ConstantInfo` for inductives, constructors, and recursors
has `value? = none`.

This is one place where we deliberately diverge in implementation
from the Aksenov paper's brief description, which is silent on how
user-defined inductives are handled. The treatment chosen here uses
each non-primitive's type expression to derive its dependency
references — the only structural information available without
unfolding the inductive's auto-generated recursor — and is
consistent with the spirit of the Aksenov formula.

## Cycle handling

The Lean environment can contain mutually recursive declarations
(rare in pure mathematics, common in Lean's elaborator core). We
break cycles by inserting a placeholder `⟨1, 1, 0⟩` for `name` before
recursing into its references; if recursion revisits `name`, the
placeholder is used. This is a lower-bound approximation for mutual
cycles and does not affect the non-mutual declarations measured by
this exe.

## Purpose

This exe backs the methodology paper's empirical claim that the
formal Lean development of `HessenbergDigraphs` exhibits the
hierarchical compression characteristic of mathematics in Aksenov
et al's sense. For comparison, Aksenov et al report Mathlib's
maximum unwrapped length at approximately 10^104 primitive terms,
in algebraic geometry.

Like `hessenberg-audit`, this file avoids static imports of the
audited modules; targets are constructed as `Name` literals and the
library is loaded at runtime via `importModules`.
-/

open Lean

/-- Count the number of `Expr` nodes in an expression. Used as a
fallback wrapped-length proxy when the declaration's `.lean` source
cannot be located (e.g. for Mathlib-side declarations whose source is
not co-located with the executable). -/
private partial def exprSize : Expr → Nat
  | .app f a => 1 + exprSize f + exprSize a
  | .lam _ t b _ => 1 + exprSize t + exprSize b
  | .forallE _ t b _ => 1 + exprSize t + exprSize b
  | .letE _ t v b _ => 1 + exprSize t + exprSize v + exprSize b
  | .mdata _ e => 1 + exprSize e
  | .proj _ _ e => 1 + exprSize e
  | _ => 1

/-- Count tokens in a Lean source slice with a hand-rolled lexer
matching Aksenov §3.2's "tokens as produced by the Lean parser".
Skips whitespace, line comments (`-- ...`), and nested block comments
(`/- ... -/`). A token is either a maximal run of identifier
characters (alphanumeric, `_`, `'`, plus `.` for qualified names) or
a single non-identifier non-whitespace character (operator or
punctuation). Lean's surface lexer treats `→`, `≤`, etc. as single
Unicode atoms, which this rule subsumes. -/
private partial def lexTokenCount (src : String) : Nat :=
  let endP : String.Pos.Raw := src.rawEndPos
  -- Identifier extension: ASCII alphanumeric or `_` `'` `.`. Unicode
  -- characters (e.g. `→`, `≤`, `θ`) are emitted as single tokens
  -- rather than extending the current identifier — an approximation
  -- of Lean's surface lexer which keeps the count well-defined and
  -- terminating.
  let isIdentExt (c : Char) : Bool :=
    c.isAlphanum || c == '_' || c == '\'' || c == '.'
  let isIdentStart (c : Char) : Bool :=
    c.isAlpha || c == '_'
  let rec skipLineComment (i : String.Pos.Raw) : String.Pos.Raw :=
    if i ≥ endP then i
    else if String.Pos.Raw.get src i == '\n' then String.Pos.Raw.next src i
    else skipLineComment (String.Pos.Raw.next src i)
  let rec skipBlockComment (i : String.Pos.Raw) (depth : Nat) : String.Pos.Raw :=
    if i ≥ endP || depth == 0 then i
    else
      let c := String.Pos.Raw.get src i
      let i' := String.Pos.Raw.next src i
      if i' ≥ endP then i'
      else
        let c' := String.Pos.Raw.get src i'
        if c == '/' && c' == '-' then
          skipBlockComment (String.Pos.Raw.next src i') (depth + 1)
        else if c == '-' && c' == '/' then
          skipBlockComment (String.Pos.Raw.next src i') (depth - 1)
        else
          skipBlockComment i' depth
  let rec eatIdent (i : String.Pos.Raw) : String.Pos.Raw :=
    if i ≥ endP then i
    else if isIdentExt (String.Pos.Raw.get src i) then
      eatIdent (String.Pos.Raw.next src i)
    else i
  let rec loop (i : String.Pos.Raw) (count : Nat) : Nat :=
    if i ≥ endP then count
    else
      let c := String.Pos.Raw.get src i
      let i' := String.Pos.Raw.next src i
      if c.isWhitespace then loop i' count
      else if c == '-' && i' < endP && String.Pos.Raw.get src i' == '-' then
        loop (skipLineComment (String.Pos.Raw.next src i')) count
      else if c == '/' && i' < endP && String.Pos.Raw.get src i' == '-' then
        loop (skipBlockComment (String.Pos.Raw.next src i') 1) count
      else if isIdentStart c || c.isDigit then
        loop (eatIdent i) (count + 1)
      else
        -- Single-char token: ASCII operator/punctuation OR a Unicode
        -- char like `→`, `≤`, `θ`, `ℕ`. Always advances by one.
        loop i' (count + 1)
  loop 0 0

/-- Locate the `.lean` source file for a declaration. Looks up the
module the declaration was defined in and converts the dotted module
name into a relative path with `.lean` extension. The lake exe runs
with `cwd = lean/` (the package root), so a relative path resolves
for declarations in this project. Returns `none` when the source is
not on the path (e.g. Mathlib-side declarations). -/
private def declSourcePath (env : Environment) (name : Name) :
    IO (Option System.FilePath) := do
  let some modIdx := env.getModuleIdxFor? name | return none
  let some modName := env.header.moduleNames[modIdx.toNat]? | return none
  let sep := System.FilePath.pathSeparator.toString
  let candidate : System.FilePath :=
    System.FilePath.mk (modName.toString.replace "." sep ++ ".lean")
  if (← candidate.pathExists) then return some candidate
  return none

/-- Source-token wrapped length per Aksenov §3.2: count tokens in the
declaration's source. Returns `none` when the source `.lean` file
or the declaration's `DeclarationRange` cannot be located; the caller
should then fall back to the `exprSize` proxy. -/
private def sourceTokens (env : Environment) (name : Name) : IO (Option Nat) := do
  let some path ← declSourcePath env name | return none
  let some ranges := Lean.declRangeExt.find? env name | return none
  let src ← IO.FS.readFile path
  let fileMap := Lean.FileMap.ofString src
  let startPos := fileMap.ofPosition ranges.range.pos
  let endPos := fileMap.ofPosition ranges.range.endPos
  let slice := String.Pos.Raw.extract src startPos endPos
  return some (lexTokenCount slice)

/-- Sentinel name used to inject `Sort` as a primitive reference into
the dependency graph. Aksenov §3.2 counts `Sort` alongside Lean-core
constants as primitives; their `collectElems` (§3.1) emits a Sort
reference for every `.sort` node. Since `Sort` is an `Expr` constructor
rather than a `ConstantInfo`, we route it through this sentinel name
and special-case it in `computeMetrics` to return `(1, 1, 0)`. The name
is never looked up in the environment. -/
private def sortPrimitive : Name := .str .anonymous "_aksenov_sort_primitive"

/-- Collect const references in an expression, weighted by occurrence
count. Matches the `collectElems` snippet in Aksenov §3.1, including
the `.sort` case which is routed to the `sortPrimitive` sentinel. -/
private partial def collectConstRefs (e : Expr)
    (acc : NameMap Nat := {}) : NameMap Nat :=
  match e with
  | .const n _ => acc.insert n ((acc.find? n).getD 0 + 1)
  | .sort _ => acc.insert sortPrimitive ((acc.find? sortPrimitive).getD 0 + 1)
  | .app f a => collectConstRefs a (collectConstRefs f acc)
  | .lam _ t b _ => collectConstRefs b (collectConstRefs t acc)
  | .forallE _ t b _ => collectConstRefs b (collectConstRefs t acc)
  | .letE _ t v b _ =>
      collectConstRefs b (collectConstRefs v (collectConstRefs t acc))
  | .mdata _ e => collectConstRefs e acc
  | .proj _ _ e => collectConstRefs e acc
  | _ => acc

/-- Aksenov-style metrics for a single declaration. -/
structure Metrics where
  wrapped : Nat
  unwrapped : Nat
  depth : Nat
  deriving Repr, Inhabited

/-- `true` iff `name` is declared in a Lean core module (one whose
module name starts with `Init` or `Lean`). Per Aksenov §3.2 these
constitute the primitives. -/
private def isLeanCorePrimitive (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | none => false
    | some m =>
      let s := m.toString
      s == "Init" || s.startsWith "Init."
        || s == "Lean" || s.startsWith "Lean."

/-- Compute compression metrics for `name`, memoising in `cache`.

Following Aksenov §3.2 exactly: the unwrapped length of a
non-primitive is the weighted sum of its references' unwrapped
lengths (no self-contribution). Primitives have unwrapped length 1
and depth 0. -/
private partial def computeMetrics
    (env : Environment) (cache : IO.Ref (NameMap Metrics))
    (name : Name) : IO Metrics := do
  if let some m := (← cache.get).find? name then
    return m
  -- Placeholder to break cycles during recursion.
  cache.modify (·.insert name ⟨1, 1, 0⟩)
  let result : Metrics ← do
    -- Sort sentinel: (1, 1, 0), Aksenov §3.2 lists `Sort` as primitive.
    if name == sortPrimitive then
      pure ⟨1, 1, 0⟩
    -- Lean-core primitives: (1, 1, 0) per Aksenov §3.2.
    else if isLeanCorePrimitive env name then
      pure ⟨1, 1, 0⟩
    else
      match env.find? name with
      | none =>
        -- Unknown name: treat as primitive (defensive default).
        pure ⟨1, 1, 0⟩
      | some info =>
        -- For non-primitives with no value (inductives, constructors,
        -- recursors, opaques), derive references from the type
        -- expression instead.
        let body := info.value?.getD info.type
        let wrapped := exprSize body
        let refs := collectConstRefs body
        let mut unwrappedSum : Nat := 0
        let mut maxDepth : Nat := 0
        let mut anyRef := false
        for (r, m) in refs.toList do
          anyRef := true
          let mr ← computeMetrics env cache r
          unwrappedSum := unwrappedSum + m * mr.unwrapped
          maxDepth := Nat.max maxDepth mr.depth
        -- If a non-primitive has no const refs (an edge case: e.g.,
        -- a function whose body uses only bound variables, or a type
        -- that is literally `Sort`), give it minimal unwrapped 1 so
        -- it is not confused with a primitive.
        let unwrapped := if anyRef then unwrappedSum else 1
        let depth := if anyRef then maxDepth + 1 else 0
        pure ⟨wrapped, unwrapped, depth⟩
  cache.modify (·.insert name result)
  return result

/-- Convenience: paper-namespace name. -/
private def hd (s : String) : Name :=
  .str (.str .anonymous "HessenbergDigraphs") s

/-- `Matrix.<s>` for the relocated matrix-side public surface. -/
private def mx (s : String) : Name :=
  .str (.str .anonymous "Matrix") s

/-- `HessenbergDigraphs.OrthogonalHessenberg.<s>`. -/
private def hdoh (s : String) : Name :=
  .str (.str (.str .anonymous "HessenbergDigraphs") "OrthogonalHessenberg") s

/-- Target declarations to measure. Subset of `Audit.publicTheorems` /
`publicDefs`, focused on the apex theorem, its three conjuncts, and
the main supporting theorems that carry the bulk of the mathematical
content. -/
private def targets : List (Name × String) :=
  [ (hd "classification",            "apex theorem")
  , (hd "completeness",              "realizability conjunct")
  , (hd "digraph_model",             "bridge conjunct")
  , (hd "rigid",                     "rigidity conjunct")
  , (hd "singleton_iso",             "singleton isomorphism")
  , (hd "singleton_iso_unique",      "singleton uniqueness")
  , (hd "loopless_iff",              "loopless characterization")
  , (hd "count_formula",             "enumeration formula")
  , (hd "count_loopless_formula",    "loopless enumeration")
  , (hdoh "exists_givensFactorization", "universality")
  , (hd "Arc",                       "support digraph arcs (def)")
  , (hd "activeSet",                 "active set extraction (def)")
  , (mx "givensProduct",             "canonical Givens product (def)") ]

/-- Pad a string on the right with spaces to width `w`. -/
private def padRight (s : String) (w : Nat) : String :=
  if s.length ≥ w then s else s ++ String.ofList (List.replicate (w - s.length) ' ')

/-- Pad a string on the left with spaces to width `w`. -/
private def padLeft (s : String) (w : Nat) : String :=
  if s.length ≥ w then s else String.ofList (List.replicate (w - s.length) ' ') ++ s

/-- Render a possibly-large `Nat` compactly. Small values print
exactly; values too large for `UInt64` print in scientific notation
as `d.dde+ee` with three significant digits. -/
private def fmtNat (n : Nat) : String :=
  let s := toString n
  if s.length ≤ 12 then s
  else
    let head := s.take 3
    let exp := s.length - 1
    s!"{head.take 1}.{head.drop 1}e+{exp}"

def main : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules
    #[(`HessenbergDigraphs : Import)] {} (trustLevel := 0)

  IO.println "HessenbergDigraphs compression analysis"
  IO.println "======================================="
  IO.println "Aksenov et al, arXiv:2603.20396 §3.1–§3.2."
  IO.println "Unwrapped formula: |u|_G = Σ wᵢ · |vᵢ|_G (Aksenov §3.2)."
  IO.println "Primitives: Lean-core declarations (Init.*, Lean.*) and Sort."
  IO.println ""

  let cache : IO.Ref (NameMap Metrics) ← IO.mkRef ({} : NameMap Metrics)

  let header :=
    padRight "declaration" 50 ++ "  " ++
    padLeft  "wrapped" 10 ++ "  " ++
    padLeft  "unwrapped" 30 ++ "  " ++
    padLeft  "depth" 6
  IO.println header
  IO.println (String.ofList (List.replicate header.length '-'))

  let mut found := 0
  let mut missing := 0
  let mut anyFallback := false
  for (name, _role) in targets do
    if env.contains name then
      found := found + 1
      let m ← computeMetrics env cache name
      let srcTokens ← sourceTokens env name
      let wrappedStr := match srcTokens with
        | some n => toString n
        | none => toString m.wrapped ++ "*"
      if srcTokens.isNone then anyFallback := true
      let row :=
        padRight name.toString 50 ++ "  " ++
        padLeft wrappedStr 10 ++ "  " ++
        padLeft (fmtNat m.unwrapped) 30 ++ "  " ++
        padLeft (toString m.depth) 6
      IO.println row
    else
      missing := missing + 1
      IO.println s!"  ✗ {name} — NOT FOUND in environment"

  IO.println ""
  IO.println s!"{found} targets measured, {missing} missing."
  if anyFallback then
    IO.println "(* = source unavailable; wrapped shown as Expr-node-count fallback)"
  IO.println ""
  IO.println "Reference: Aksenov et al report Mathlib's maximum"
  IO.println "unwrapped length at approximately 1e104 primitive terms."

  return 0
