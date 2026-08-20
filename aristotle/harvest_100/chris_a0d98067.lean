import Mathlib

/-!
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-- Auxiliary: `n + 1` divides the central binomial coefficient `C(2n, n)`.
This is what makes the natural-number division in the closed form exact. -/
theorem succ_dvd_choose_two_mul (n : ℕ) : (n + 1) ∣ Nat.choose (2 * n) n := by
  simpa [Nat.centralBinom] using Nat.succ_dvd_centralBinom n

/-- **Closed form for the Catalan numbers.**
The `n`-th Catalan number equals `C(2n, n) / (n + 1)` (natural-number division,
which is exact here by `succ_dvd_choose_two_mul`).
This follows from Mathlib's `catalan_eq_centralBinom_div` together with the
definition `Nat.centralBinom n = Nat.choose (2 * n) n`. -/
theorem catalan_closed (n : ℕ) : catalan n = Nat.choose (2 * n) n / (n + 1) := by
  simpa [Nat.centralBinom] using catalan_eq_centralBinom_div n

/-- Division-free restatement: `(n + 1) * catalan n = C(2n, n)`. -/
theorem catalan_closed_mul (n : ℕ) : (n + 1) * catalan n = Nat.choose (2 * n) n := by
  obtain ⟨k, hk⟩ := succ_dvd_choose_two_mul n
  rw [catalan_closed, hk, Nat.mul_div_cancel_left _ (Nat.succ_pos n)]

/-- Rational form of the closed formula: `catalan n = C(2n, n) / (n + 1)` in `ℚ`. -/
theorem catalan_closed_rat (n : ℕ) :
    (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) / (n + 1) := by
  rw [eq_div_iff (by positivity)]
  exact_mod_cast (by rw [mul_comm]; exact catalan_closed_mul n :
    catalan n * (n + 1) = Nat.choose (2 * n) n)

end Math

