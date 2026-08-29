/-
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment at the very top of the file: Lean 4 requires
`import` commands to precede any module docstring.)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Brockian

/-- The wheel modulus considered here. -/

lemma prime_of_isPrimeB {n : ℕ} (hn : n ≤ 1680) (h : isPrimeB n = true) : n.Prime := by
  have h2 : 2 ≤ n := by
    have := (Bool.and_eq_true_iff.mp h).1
    simpa using this
  by_contra hnp
  have hcomp : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hmp : (n.minFac).Prime := Nat.minFac_prime (by omega)
  have hm2 := hmp.two_le
  have hsq : n.minFac * n.minFac ≤ n := by nlinarith [hcomp]
  have hmem : n.minFac ∈ trialBasis := mem_trialBasis_of_prime hmp (by omega)
  have hall := (Bool.and_eq_true_iff.mp h).2
  have hx := List.all_eq_true.mp hall _ hmem
  have hdvd : n % n.minFac = 0 := Nat.dvd_iff_mod_eq_zero.mp (Nat.minFac_dvd n)
  simp [hdvd] at hx
  have : n.minFac < n := by nlinarith
  omega

/-- From a successful boolean Goldbach test we get an actual pair of primes. -/
