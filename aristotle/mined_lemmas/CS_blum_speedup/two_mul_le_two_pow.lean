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


theorem two_mul_le_two_pow : ∀ m : ℕ, 4 ≤ m → 2 * m ≤ 2 ^ m := by
  intro m hm
  induction m with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> simp_all
    · have h1 := ih (by omega)
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      omega

