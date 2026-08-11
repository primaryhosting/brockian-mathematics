/-!
# Two Squares 73
Category: Pure Mathematics
Target: Math.two_squares_73
Statement: The prime 73 is a sum of two squares.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- The prime 73 is a sum of two squares: `73 = 3^2 + 8^2`. -/
theorem two_squares_73 : Nat.Prime 73 ∧ ∃ a b : ℕ, (73 : ℕ) = a ^ 2 + b ^ 2 := by
  refine ⟨by norm_num, 3, 8, by norm_num⟩

end Math

