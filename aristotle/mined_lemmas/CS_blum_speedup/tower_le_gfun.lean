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


theorem tower_le_gfun (x : ℕ) : 2 ^ 2 ^ x ≤ gfun (x + 1) := by
  induction x with
  | zero => decide
  | succ n ih =>
    have h1 := sq_le_pair (n + 2) (gfun (n + 1))
    have h2 : 2 ^ 2 ^ (n + 1) = (2 ^ 2 ^ n) * (2 ^ 2 ^ n) := by rw [← pow_add]; ring_nf
    calc 2 ^ 2 ^ (n + 1) = (2 ^ 2 ^ n) * (2 ^ 2 ^ n) := h2
      _ ≤ gfun (n + 1) * gfun (n + 1) := Nat.mul_le_mul ih ih
      _ ≤ Nat.pair (n + 2) (gfun (n + 1)) := h1
      _ = gfun (n + 2) := by simp [gfun]

