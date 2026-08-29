/-!
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- Euclid's algorithm, in its modulus form.
The recursion is on the second argument, which strictly decreases at each
recursive call; the termination checker verifies this, so the function is
total: the algorithm terminates on every input. -/

theorem euclid_pos (a b : Nat) (hb : 0 < b) : euclid a b = euclid b (a % b) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  exact euclid_succ a c

/-- Euclid's algorithm computes the greatest common divisor. -/
