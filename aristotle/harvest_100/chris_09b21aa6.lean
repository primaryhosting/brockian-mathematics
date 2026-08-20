/-!
# Cassini 13
Category: Pure Mathematics
Target: Math.cassini_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean forbids any `import` after the module header comment above, so this file is
-- kept import-free (core Lean only).  The Mathlib formulation, stated with `Nat.fib` and
-- deduced from Mathlib's `Int.fib_succ_mul_fib_pred_sub_fib_sq`, lives in
-- `RequestProject/CassiniMathlib.lean`, which imports both Mathlib and this file.

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.
It agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_nat_fib`). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity** at `n = 13`: `F 12 * F 14 - F 13 ^ 2 = (-1) ^ 13`. -/
theorem cassini_13 :
    (fib 12 : Int) * (fib 14 : Int) - (fib 13 : Int) ^ 2 = (-1) ^ 13 := by
  decide

end Math

import Mathlib
import RequestProject.Main

/-!
# Cassini 13, Mathlib formulation

`Nat.fib 12 * Nat.fib 14 - Nat.fib 13 ^ 2 = (-1) ^ 13`, obtained from Mathlib's Cassini
identity `Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- **Cassini's identity** at `n = 13`, stated with Mathlib's `Nat.fib`:
`F 12 * F 14 - F 13 ^ 2 = (-1) ^ 13`.

This is the instance `n = 13` of Mathlib's `Int.fib_succ_mul_fib_pred_sub_fib_sq`,
`fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ n.natAbs` for `n : ℤ`. -/
theorem cassini_13_nat_fib :
    (Nat.fib 12 : ℤ) * (Nat.fib 14 : ℤ) - (Nat.fib 13 : ℤ) ^ 2 = (-1) ^ 13 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 13
  rw [show ((13 : ℤ) + 1) = ((14 : ℕ) : ℤ) by norm_num,
    show ((13 : ℤ) - 1) = ((12 : ℕ) : ℤ) by norm_num,
    show (13 : ℤ) = ((13 : ℕ) : ℤ) by norm_num,
    Int.fib_natCast, Int.fib_natCast, Int.fib_natCast] at h
  simpa [mul_comm] using h

end Math

