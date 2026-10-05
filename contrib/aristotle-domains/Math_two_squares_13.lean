/-!
# Two Squares 13
Category: Pure Mathematics
Target: Math.two_squares_13
Statement: The prime 13 is a sum of two squares.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- The prime 13 is a sum of two squares. -/
theorem two_squares_13 : Nat.Prime 13 ∧ ∃ a b : ℕ, 13 = a ^ 2 + b ^ 2 := by
  refine ⟨by norm_num, 2, 3, by norm_num⟩

end Math

