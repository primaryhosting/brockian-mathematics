/-!
# Two Squares 61
Category: Pure Mathematics
Target: Math.two_squares_61
Statement: The prime 61 is a sum of two squares.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- The prime 61 is a sum of two squares: `61 = 5 ^ 2 + 6 ^ 2`. -/
theorem two_squares_61 : Nat.Prime 61 ∧ ∃ a b : ℕ, 61 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 5, 6, by norm_num⟩

end Math

