/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is
-- repeated verbatim as the module docstring immediately after the import.)
import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace Frontier

/-- Every divisor of an odd natural number is odd. -/

private lemma odd_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : Odd n) : Odd m := by
  obtain ⟨k, rfl⟩ := hmn
  exact (Nat.odd_mul.mp hn).1

/-- The statement "every finite simple group of odd order is commutative".
This is the simple-group form of the Feit–Thompson odd order theorem. -/
