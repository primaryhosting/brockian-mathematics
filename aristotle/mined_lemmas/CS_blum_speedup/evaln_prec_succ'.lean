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


theorem evaln_prec_succ' {k a y : ℕ} {cf cg : Code} (h : Nat.pair a (y + 1) ≤ k) :
    evaln (k + 1) (Code.prec cf cg) (Nat.pair a (y + 1)) =
      (evaln k (Code.prec cf cg) (Nat.pair a y)).bind fun i =>
        evaln (k + 1) cg (Nat.pair a (Nat.pair y i)) := by
  simp [evaln, h]

/-! ### An a priori bound on the size of outputs -/

/-- Structural depth of a code; it controls how much a program can blow up the size of its
output relative to its running time. -/
