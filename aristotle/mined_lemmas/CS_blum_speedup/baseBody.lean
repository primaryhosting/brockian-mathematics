/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is a plain
-- block comment; its text is otherwise verbatim.)

import Mathlib

/-!
We work with Mathlib's model of computation `Nat.Partrec.Code` together with its canonical
step-indexed evaluator `Nat.Partrec.Code.evaln`.  The running time of a program `c` on input `x`
is the least step bound `k` for which `evaln k c x` returns a value.

We exhibit an explicit total computable function `gfun` (a doubly exponentially growing function)
with *no fastest program*: for every program `c` computing `gfun` there is another program `d`
computing `gfun` which is strictly faster on all but finitely many inputs.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ### Elementary arithmetic helpers -/


def baseBody : Code :=
  Code.pair (Code.comp Code.succ (Code.comp Code.left Code.right)) (Code.comp Code.right Code.right)

/-- The straightforward program computing `gfun` by a loop. -/
