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

theorem wheel_two_units_cover (r : Nat) (hr : r < 1051) :
    ∃ a b : Nat, 0 < a ∧ a < 1051 ∧ 0 < b ∧ b < 1051 ∧
      Nat.gcd a 1051 = 1 ∧ Nat.gcd b 1051 = 1 ∧ (a + b) % 1051 = r := by
  by_cases h0 : r = 0
  · subst h0
    exact ⟨1, 1050, by omega, by omega, by omega, by omega,
      gcd_1051_eq_one 1 (by omega) (by omega),
      gcd_1051_eq_one 1050 (by omega) (by omega), by omega⟩
  by_cases h1 : r = 1
  · subst h1
    exact ⟨2, 1050, by omega, by omega, by omega, by omega,
      gcd_1051_eq_one 2 (by omega) (by omega),
      gcd_1051_eq_one 1050 (by omega) (by omega), by omega⟩
  exact ⟨1, r - 1, by omega, by omega, by omega, by omega,
    gcd_1051_eq_one 1 (by omega) (by omega),
    gcd_1051_eq_one (r - 1) (by omega) (by omega), by omega⟩

/-- **Goldbach Wheel K 2, modulus 1051.**
The wheel modulus `1051` is prime; Goldbach's binary conjecture holds for every even
number up to `1051`, with both summands drawn from the wheel of primes below the
modulus; and every residue class modulo `1051` is a sum of two residues coprime to
`1051` (the `K = 2` wheel-covering condition). -/
