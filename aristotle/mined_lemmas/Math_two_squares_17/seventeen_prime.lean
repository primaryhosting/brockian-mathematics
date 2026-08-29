import Mathlib

/-!
# Two Squares 17
Category: Pure Mathematics
Target: Math.two_squares_17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `17` is prime. -/

theorem seventeen_prime : Nat.Prime 17 := by norm_num

/-- The prime `17` is a sum of two squares (indeed `17 = 1 ^ 2 + 4 ^ 2`).

The proof invokes Mathlib's `Nat.Prime.sq_add_sq`, the Fermat two-squares theorem:
every prime `p` with `p % 4 ≠ 3` is a sum of two squares. -/
