/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 100000

namespace Brockian

/-- Candidate divisors `2, 3, …, 47`: enough to certify primality below `48^2 = 2304`. -/

theorem prime_of_isPrimeB {n : ℕ} (hn : n < 2304) (h : isPrimeB n = true) : Nat.Prime n := by
  rw [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨h2, hall⟩ := h
  by_contra hp
  have hne : n ≠ 1 := by omega
  have hmp : Nat.Prime n.minFac := Nat.minFac_prime hne
  have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hp
  have hlt : n.minFac < 48 := by nlinarith [hmp.two_le, sq_nonneg n.minFac]
  have hmem : n.minFac ∈ trialDivisors := by
    rw [trialDivisors, List.mem_range'_1]
    exact ⟨hmp.two_le, by omega⟩
  have hthis := hall _ hmem
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hthis
  have hdvd : n % n.minFac = 0 := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n)
  rcases hthis with h1 | h1
  · nlinarith [hsq]
  · exact h1 hdvd

/-- The wheel of admissible small summands: all primes up to `73`. -/
