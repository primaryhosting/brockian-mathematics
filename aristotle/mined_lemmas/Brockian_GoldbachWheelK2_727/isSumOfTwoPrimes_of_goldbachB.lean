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

lemma isSumOfTwoPrimes_of_goldbachB {n : ℕ} (hn : n ≤ 1680) (h : goldbachB n = true) :
    IsSumOfTwoPrimes n := by
  obtain ⟨p, hp, hcheck⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨h1, h2⟩, h3⟩ := hcheck
  exact ⟨p, n - p, prime_of_isPrimeB (by omega) h1, prime_of_isPrimeB (by omega) h2, by omega⟩

/-- The finite verification: every even `n` with `4 ≤ n ≤ 2 * 727 + 2` passes the test. -/
