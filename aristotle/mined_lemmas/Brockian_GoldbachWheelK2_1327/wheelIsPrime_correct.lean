import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The primes below `41`; a trial-division wheel sufficient to decide primality
below `41 ^ 2 = 1681`. -/

lemma wheelIsPrime_correct {n : ℕ} (hn : n < 1681) (h : wheelIsPrime n = true) :
    Nat.Prime n := by
  rw [wheelIsPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  by_contra hnp
  set d := n.minFac with hd
  have hdp : Nat.Prime d := Nat.minFac_prime (by omega)
  have hsq : d ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hdlt : d < 41 := by nlinarith [hsq, hdp.two_le]
  have hmem : d ∈ wheelPrimes := prime_lt_41_mem_wheelPrimes d hdlt hdp
  have hdvd : n % d = 0 := Nat.dvd_iff_mod_eq_zero.mp (Nat.minFac_dvd n)
  have hlt := h2 d hmem
  simp [hdvd] at hlt
  nlinarith [hsq, hlt]

