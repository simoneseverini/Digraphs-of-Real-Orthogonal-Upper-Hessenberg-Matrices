import VersoManual
import Paper.Tikz
import HessenbergDigraphs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Paper
open HessenbergDigraphs

#doc (Manual) "Enumeration consequences" =>

Combining rigidity with the singleton coincidence
$`D_n(\{t\}) \cong D_n(\{n-t\})` yields a closed-form count of
isomorphism classes.

*Theorem 2.13 (connected count).* {name}`card_isoClasses_quot` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/Combinatorial/ClassCount.lean#L262)

For $`n \ge 2`, the number of non-isomorphic weakly connected support
digraphs of $`n \times n` unreduced orthogonal upper Hessenberg
matrices is
$$`N_n \;=\; 2^{\,n-1} \;-\; \Big\lfloor \tfrac{n-1}{2} \Big\rfloor.`

{docstring card_isoClasses_quot}

*Theorem 2.14 (loopless count).* {name}`card_looplessClasses_quot` [✓](https://github.com/simoneseverini/Digraphs-of-Real-Orthogonal-Upper-Hessenberg-Matrices/blob/main/lean/HessenbergDigraphs/Combinatorial/ClassCount.lean#L516)

For $`n \ge 3`, the number of non-isomorphic loopless connected support
digraphs is
$$`N_n^{\mathrm{loopless}} \;=\; F_{n-1} \;-\; \Big\lfloor \tfrac{n-3}{2} \Big\rfloor,`
where $`F_k` is the $`k`-th Fibonacci number ($`F_0 = 0`, $`F_1 = 1`).

{docstring card_looplessClasses_quot}

*Proof sketch (both counts).*
Both counts follow the same template: _labeled_ configurations are
subsets $`S \subseteq [n-1]` (resp. $`S \subseteq \{2, \dots, n-2\}`
with no consecutive elements, the loopless characterisation). The
number of labeled configurations is $`2^{n-1}` (resp. $`F_{n-1}` via
the standard Fibonacci-counts-binary-strings bijection). Subsets with
$`|S| \ge 2` are rigid (Theorem 2.10), so each is its own isomorphism
class. The empty subset is rigid alone. The $`|S| = 1` subsets pair up
under $`\{t, n-t\}`, contributing $`\lceil(n-1)/2\rceil` (resp.
$`\lceil(n-3)/2\rceil`) classes.
