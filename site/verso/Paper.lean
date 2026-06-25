import VersoManual
import Paper.Tikz
import Paper.Setup
import Paper.Theorems
import Paper.Enumeration

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Digraphs of real orthogonal upper Hessenberg matrices" =>

A complete classification of the support digraphs of real orthogonal upper
Hessenberg matrices, formalised in Lean 4. This site is the Verso rendering
of the paper's mathematical content; the formal Lean development is the
primary artifact, and this rendering is a human-facing companion. Each main
theorem carries a green checkmark linking to its Lean declaration.

{include 1 Paper.Setup}

{include 1 Paper.Theorems}

{include 1 Paper.Enumeration}
