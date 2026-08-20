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

theorem primeCheck_iff (n : Nat) : primeCheck n = true ↔ IsPrimeNat n := by
  simp only [primeCheck, IsPrimeNat, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hm2 => ?_⟩
    rcases h m hm with h' | h'
    · omega
    · simpa using h'
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm => ?_⟩
    by_cases hm2 : 2 ≤ m
    · exact Or.inr (by simpa using h m hm hm2)
    · exact Or.inl (by omega)

instance : DecidablePred IsPrimeNat := fun n => decidable_of_iff _ (primeCheck_iff n)

/-- The wheel: all primes up to the wheel modulus `1051`. -/
