/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Brockian

/-- Elementary primality predicate: `p` is at least `2` and its only divisors are `1` and `p`. -/

theorem hasRep_spec {n : Nat} (h : hasRep n = true) :
    ∃ p q, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = n := by
  obtain ⟨a, b, ha, hb, hab⟩ := hasRepAux_spec n (n + 1) 2 h
  exact ⟨a, b, isPrimeB_spec ha, isPrimeB_spec hb, hab⟩

/-- **Goldbach wheel, `K = 2`, modulus `947`.**
Every even `n` with `4 ≤ n ≤ 947` is a sum of two primes. -/
