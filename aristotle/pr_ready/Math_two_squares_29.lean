/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Statement: The prime 29 is a sum of two squares.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- **Two squares for 29.** The number `29` is prime, and it is a sum of two squares,
namely `29 = 2 ^ 2 + 5 ^ 2`. -/
theorem two_squares_29 : Nat.Prime 29 ∧ ∃ a b : ℕ, 29 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 2, 5, by norm_num⟩

end Math

