/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
set_option autoImplicit false

namespace Brockian

/-- Primality of a natural number, spelled out. This is equivalent to `Nat.Prime`; the
equivalence and a Mathlib-phrased restatement are in `RequestProject.Main`. -/

theorem isPrimeB_two_le {n : Nat} (h : isPrimeB n = true) : 2 ≤ n := by
  rw [isPrimeB, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

/-- Correctness of the fast primality test in the range where it is used. -/
