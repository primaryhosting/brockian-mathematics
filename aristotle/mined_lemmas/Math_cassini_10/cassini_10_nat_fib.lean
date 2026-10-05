import Mathlib
import RequestProject.Main

/-!
# Cassini's identity at `n = 10`, in Mathlib terms

This file links the self-contained `Math.fib` of `RequestProject/Main.lean` with Mathlib's
`Nat.fib`, and restates `Math.cassini_10` using `Nat.fib`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini_10_nat_fib :
    (Nat.fib 9 : ℤ) * (Nat.fib 11 : ℤ) - (Nat.fib 10 : ℤ) ^ 2 = (-1) ^ 10 := by
  simpa [fib_eq_nat_fib] using cassini_10

end Math

/-!
# Cassini 10
Category: Pure Mathematics
Target: Math.cassini_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, with `fib 0 = 0` and `fib 1 = 1`.
(This file must begin with the module docstring above, which Lean requires to precede any
`import`; the theory here is therefore stated with a self-contained definition of `fib`.
The file `RequestProject/Cassini.lean` proves that this `fib` agrees with Mathlib's `Nat.fib`
and restates the identity in Mathlib terms.) -/
