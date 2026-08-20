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

theorem isPrimeNat_iff_natPrime (n : ℕ) : IsPrimeNat n ↔ Nat.Prime n := by
  rw [Nat.prime_def_lt]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hdvd => ?_⟩
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · interval_cases m
      · simp at hdvd; omega
      · rfl
    · exact absurd (Nat.mod_eq_zero_of_dvd hdvd) (h m hm hge)
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hge hmod => ?_⟩
    have : m ∣ n := Nat.dvd_of_mod_eq_zero hmod
    have := h m hm this
    omega

/-- Goldbach's binary conjecture (Mathlib's `Nat.Prime`), verified for every even
number up to the wheel modulus `1051`. -/
