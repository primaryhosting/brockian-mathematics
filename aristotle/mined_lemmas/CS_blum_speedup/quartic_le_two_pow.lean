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


theorem quartic_le_two_pow : ∀ t : ℕ, 20 ≤ t → (t + 2) ^ 4 + t + 4 ≤ 2 ^ t := by
  intro t ht
  induction t with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 20 with h | h
    · have hn : n = 19 := by omega
      subst hn; norm_num
    · have h1 := ih (by omega)
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      have h4 : n ^ 4 = n * (n * n * n) := by ring
      have h5 : 20 * (n * n * n) ≤ n * (n * n * n) := Nat.mul_le_mul_right _ h
      have h3 : (n + 3) ^ 4 + n + 5 ≤ 2 * ((n + 2) ^ 4 + n + 4) := by nlinarith [h5, h]
      show (n + 3) ^ 4 + (n + 1) + 4 ≤ 2 ^ (n + 1)
      omega

