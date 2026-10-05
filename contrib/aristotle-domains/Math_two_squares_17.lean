/-!
# Two Squares 17
Category: Pure Mathematics
Target: Math.two_squares_17
Statement: The prime 17 is a sum of two squares.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- The prime 17 is a sum of two squares: `17 = 1^2 + 4^2`. -/
theorem two_squares_17 : Nat.Prime 17 ∧ ∃ a b : ℕ, 17 = a ^ 2 + b ^ 2 := by
  refine ⟨by norm_num, 1, 4, by norm_num⟩

end Math

