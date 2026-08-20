/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Brockian

/-- The wheel modulus of this member of the `GoldbachWheelK2` family. -/

theorem wheel_two_units_cover_coprime (r : ℕ) (hr : r < wheelModulus) :
    ∃ a b : ℕ, 0 < a ∧ a < wheelModulus ∧ 0 < b ∧ b < wheelModulus ∧
      Nat.Coprime a wheelModulus ∧ Nat.Coprime b wheelModulus ∧
      (a + b) % wheelModulus = r :=
  wheel_two_units_cover r hr

end Brockian

