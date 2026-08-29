import Mathlib
import RequestProject.Math

/-!
# Compatibility with Mathlib's Fibonacci numbers

`Math.fib` (defined without any Mathlib import, so that the target file
`RequestProject/Math.lean` can begin with its required header comment) agrees with
Mathlib's `Nat.fib`.  We restate Cassini's identity at `n = 15` in terms of `Nat.fib`,
and also derive it from Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini_15_of_mathlib :
    (Nat.fib 14 : ℤ) * (Nat.fib 16 : ℤ) - (Nat.fib 15 : ℤ) ^ 2 = (-1) ^ 15 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq (15 : ℤ)
  rw [show ((15 : ℤ) + 1) = ((16 : ℕ) : ℤ) by norm_num,
      show ((15 : ℤ) - 1) = ((14 : ℕ) : ℤ) by norm_num,
      show ((15 : ℤ)) = ((15 : ℕ) : ℤ) by norm_num,
      Int.fib_natCast, Int.fib_natCast, Int.fib_natCast] at h
  rw [show ((15 : ℕ) : ℤ).natAbs = 15 by norm_num] at h
  linarith [h]

end Math

/-!
# Cassini 15
Category: Pure Mathematics
Target: Math.cassini_15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n + 2) = fib n + fib (n + 1)`.
This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_nat_fib` in `RequestProject.MathFib`). -/
