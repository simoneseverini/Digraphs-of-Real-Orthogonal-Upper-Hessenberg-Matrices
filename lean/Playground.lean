/-
Copyright (c) 2026 Xinze Li, Simone Severini. All rights reserved.
Released under Apache 2.0 license as described in the file lean/LICENSE.
Authors: Xinze Li, Simone Severini
-/
import HessenbergDigraphs.Command

/-!
# Playground — try the verified Hessenberg digraph calculator

Every output is backed by a correctness theorem from the library.
Delete or modify freely; this file is not imported by the library.

## Available commands

* `#hessenberg n {k₁, k₂, …}` — full profile of `D_n(S)`.
* `#hessenberg_count n` — isomorphism class counts.
-/

open scoped HessenbergDigraphs

-----------------------------------------------------------------------
-- Paper examples
-----------------------------------------------------------------------

-- Figure 2: D_6({2, 4})
#hessenberg 6 {2, 4}

-- §5: D_5({2}) — loopless singleton
#hessenberg 5 {2}

-- D_5({1, 3}) — has a loop at v1
#hessenberg 5 {1, 3}

-----------------------------------------------------------------------
-- Classification counts
-----------------------------------------------------------------------

#hessenberg_count 6
#hessenberg_count 8
#hessenberg_count 10


-----------------------------------------------------------------------
-- Try your own below
-----------------------------------------------------------------------

#hessenberg 8 {1, 3, 5, 7}
#hessenberg 4 {2}
#hessenberg 7 {2, 4, 6}
#hessenberg 11 {1, 3, 5, 7, 9}
#hessenberg 12 {2, 4, 6, 8, 10}
#hessenberg 15 {1, 3, 5, 7, 9, 11}