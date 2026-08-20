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

theorem goldbach_le_1051_natPrime (n : ℕ) (hev : Even n) (h4 : 4 ≤ n) (hle : n ≤ wheelModulus) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  have hmod : n % 2 = 0 := Nat.even_iff.mp hev
  obtain ⟨p, q, hp, hq, hpq⟩ := goldbach_le_1051 n hmod h4 hle
  exact ⟨p, q, (isPrimeNat_iff_natPrime p).mp hp, (isPrimeNat_iff_natPrime q).mp hq, hpq⟩

/-- The `K = 2` wheel-covering condition, phrased with `Nat.Coprime`: every residue
class modulo the wheel modulus `1051` is a sum of two residues coprime to it. -/
