/-!
# Two Squares 97
Category: Pure Mathematics
Target: Math.two_squares_97
Statement: The prime 97 is a sum of two squares.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- The prime 97 is a sum of two squares: `97 = 4^2 + 9^2`. -/
theorem two_squares_97 : Nat.Prime 97 ∧ ∃ a b : ℕ, 97 = a ^ 2 + b ^ 2 := by
  refine ⟨by norm_num, 4, 9, by norm_num⟩

end Math

