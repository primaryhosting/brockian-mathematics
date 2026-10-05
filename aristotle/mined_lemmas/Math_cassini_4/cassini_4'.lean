/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` commands to precede every other command, including
-- module docstrings, so this module is kept dependency-free (the header above must be
-- the first thing in the file). The Fibonacci sequence is therefore defined here, and
-- `RequestProject/Main.lean` (which does import Mathlib) proves that it agrees with
-- `Nat.fib` and re-derives the statement from Mathlib's Cassini identity
-- `Int.fib_succ_mul_fib_pred_sub_fib_sq`.

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n + 2) = F n + F (n + 1)`. -/

theorem cassini_4' :
    (Math.fib 3 : ℤ) * (Math.fib 5 : ℤ) - (Math.fib 4 : ℤ) ^ 2 = (-1 : ℤ) ^ 4 := by
  simpa [fib_eq_nat_fib] using cassini_4_nat_fib

end Math

