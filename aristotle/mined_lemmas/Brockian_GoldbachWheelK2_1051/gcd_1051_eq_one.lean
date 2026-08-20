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

theorem gcd_1051_eq_one (b : Nat) (hb : 0 < b) (hlt : b < 1051) : Nat.gcd b 1051 = 1 := by
  have hprime : IsPrimeNat 1051 := by decide
  have hdvd : Nat.gcd b 1051 ∣ 1051 := Nat.gcd_dvd_right _ _
  have hdb : Nat.gcd b 1051 ∣ b := Nat.gcd_dvd_left _ _
  have hdle : Nat.gcd b 1051 ≤ b := Nat.le_of_dvd hb hdb
  have hdlt : Nat.gcd b 1051 < 1051 := Nat.lt_of_le_of_lt hdle hlt
  by_cases h2 : 2 ≤ Nat.gcd b 1051
  · exact absurd (Nat.mod_eq_zero_of_dvd hdvd) (hprime.2 _ hdlt h2)
  · have hd0 : Nat.gcd b 1051 ≠ 0 := by
      intro h
      rw [h] at hdvd
      exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (by decide)
    omega

/-- The `K = 2` wheel-covering condition at the modulus `1051`: every residue class
modulo `1051` is the sum of two residues that are nonzero and coprime to `1051`. -/
