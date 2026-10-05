/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses a plain block comment rather than a `/-! -/` module docstring,
-- because Lean 4 requires `import` commands to precede any doc comment.)

import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- The `K = 2` wheel class condition: a natural number is admissible as a summand in a
`K = 2` Goldbach decomposition modulo the wheel `2 * 3 = 6` exactly when it is coprime to `6`. -/

theorem wheelK2_of_prime {p : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) : WheelK2 p := by
  have h2 : Nat.Coprime p 2 := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have h3 : Nat.Coprime p 3 := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_
    have := Nat.le_of_dvd (by norm_num) h
    omega
  show Nat.Coprime p (2 * 3)
  exact Nat.Coprime.mul_right h2 h3

/-- **Goldbach wheel, `K = 2`, modulus `947`.**
The even number `2 * 947 = 1894` is the sum of two primes, and both summands lie in the
`K = 2` wheel classes (they are coprime to `6`), and are moreover coprime to the wheel
modulus `947`. -/
