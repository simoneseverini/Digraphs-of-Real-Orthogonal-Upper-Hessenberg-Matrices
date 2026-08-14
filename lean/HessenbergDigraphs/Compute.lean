/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li, Simone Severini
-/
import HessenbergDigraphs.Compute.Repr
import HessenbergDigraphs.Compute.Enumerate
import HessenbergDigraphs.Compute.Query

/-!
# `Compute` layer facade

Entry point for the verified computation layer of `HessenbergDigraphs`.
Re-exports the three submodules so downstream code (notably the
`#hessenberg` / `#hessenberg_count` commands in `Command`) can depend on
a single import:

* `Compute.Repr` — `Repr` instances for displaying `ActiveSet n` and its
  derived data.
* `Compute.Enumerate` — executable enumerators (active sets, isomorphism
  classes) matching the formal `Finset` constructions.
* `Compute.Query` — computable property queries, each certified against
  the Prop-level result proved in the `Combinatorial` tier.

This module introduces no new declarations; it exists only to bundle the
public compute API.
-/
