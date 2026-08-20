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

theorem wheel_le_181 : ∀ p ∈ goldbachWheelK2, p ≤ 181 := by
  intro p hp
  have h : goldbachWheelK2.all (fun p => decide (p ≤ 181)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h p hp)

/-- **Goldbach wheel, K = 2, modulus 727.**
Every even `n` with `4 ≤ n ≤ 2 * 727 = 1454` is a sum of two primes, one of which lies in the
fixed 12-element wheel `Brockian.goldbachWheelK2`. -/
