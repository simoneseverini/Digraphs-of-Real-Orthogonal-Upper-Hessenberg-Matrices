/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import Lean

/-!
# `linter.hessenbergMathTag`

Project-specific syntax linter. Enforces that every top-level
declaration whose docstring is present begins with one of the tags
`**Math.**`, `**Eng.**`, or `**Mixed.**`.

The Math / Eng / Mixed convention is described in the methodology
paper accompanying this library and is inherited from
mathematical tradition rather than derived from the prose paper. A
declaration is `**Math.**` when it directly corresponds to a paper-side
mathematical concept, `**Eng.**` when it encodes type-theoretic
plumbing with no paper analogue, `**Mixed.**` when a paper-side
mathematical statement is established by an engineering-heavy proof
body.

This linter does not require a docstring; it only checks the tag when
a docstring is present. Declarations with no docstring are silently
skipped — the convention is opt-in per declaration.

Activated via `set_option linter.hessenbergMathTag true`. Default is
`false` at file level; enabled project-wide via
`weak.linter.hessenbergMathTag` in the lakefile.

To silence locally use `set_option linter.hessenbergMathTag false in <decl>`,
or supply the appropriate tag.
-/

open Lean Elab Linter

namespace HessenbergDigraphs.Linter.MathTag

/-- The HessenbergDigraphs Math/Eng/Mixed docstring-tag linter option. -/
register_option linter.hessenbergMathTag : Bool := {
  defValue := false
  descr := "Enforce **Math.**/**Eng.**/**Mixed.** docstring tag on declarations."
}

/-- Accepted tag prefixes for declarations. -/
private def acceptedTags : List String := ["**Math.**", "**Eng.**", "**Mixed.**"]

private def hasAcceptedTag (s : String) : Bool :=
  let s := s.trimAsciiStart.toString
  acceptedTags.any fun tag => s.startsWith tag

/-- The Math/Eng/Mixed-tag linter. Fires only on top-level declaration
commands (`def`, `theorem`, `lemma`, `abbrev`, `instance`, `class`,
`structure`, `inductive`, ...). Structure fields, class fields, and
other nested constructs are skipped — the tagging convention applies
to whole declarations, not internal slots. -/
def mathTagLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.hessenbergMathTag (← getLinterOptions) do return
  unless stx.isOfKind ``Lean.Parser.Command.declaration do return
  let docStx := stx[0][0][0]
  if docStx.isMissing then return
  let docString ← try getDocStringText ⟨docStx⟩ catch _ => return
  unless hasAcceptedTag docString do
    let preview := (docString.trimAsciiStart.toString.take 40).replace "\n" " "
    Linter.logLint linter.hessenbergMathTag docStx
      m!"docstring should start with **Math.**, **Eng.**, or **Mixed.** \
         (got: \"{preview}…\")"

initialize addLinter mathTagLinter

end HessenbergDigraphs.Linter.MathTag
