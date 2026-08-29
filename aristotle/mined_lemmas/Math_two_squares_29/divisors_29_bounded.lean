/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `IsPrimeNat p` says that `p` is a prime natural number: it is at least `2`
and its only divisors are `1` and itself.

(The required header of this file is a module docstring, which Lean requires to
come after any `import`; consequently this file is self-contained and does not
import Mathlib, so primality is spelled out here.) -/

theorem divisors_29_bounded : ∀ d : Nat, d < 30 → d ∣ 29 → d = 1 ∨ d = 29 := by
  decide

/-- `29` is prime. -/
