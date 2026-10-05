/-!
# Two Squares 113
Category: Pure Mathematics
Target: Math.two_squares_113
Statement: The prime 113 is a sum of two squares.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- The prime 113 is a sum of two squares: `113 = 7^2 + 8^2`. -/
theorem two_squares_113 : Nat.Prime 113 ∧ ∃ a b : ℕ, 113 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 7, 8, by norm_num⟩

end Math

