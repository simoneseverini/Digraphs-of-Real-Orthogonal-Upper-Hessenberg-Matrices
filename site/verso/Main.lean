import VersoManual
import Paper

open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  manualMain (text := %doc Paper) (options := args)
