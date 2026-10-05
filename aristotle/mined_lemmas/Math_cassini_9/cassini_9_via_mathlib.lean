/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.
This agrees with Mathlib's `Nat.fib` (see `RequestProject/CassiniMathlib.lean`). -/

theorem cassini_9_via_mathlib :
    Int.fib (9 + 1) * Int.fib (9 - 1) - Int.fib 9 ^ 2 = (-1) ^ (9 : ℤ).natAbs :=
  Int.fib_succ_mul_fib_pred_sub_fib_sq 9

end Math

