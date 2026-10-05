import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The full Catalan–Mihăilescu statement: `8` and `9` are the only consecutive
perfect powers, i.e. the only solution of `x ^ p = y ^ q + 1` in integers
`x, y, p, q > 1` is `3 ^ 2 = 2 ^ 3 + 1`. -/

lemma pow_two_dvd_choose_mul {r j e : ℕ} (hj : 2 ≤ j)
    (he : 2 ^ e ∣ r.choose 2) : 2 ^ e ∣ r.choose (2 * j) * j := by
  have hid : r.choose (2 * j) * (2 * j).choose 2 = r.choose 2 * (r - 2).choose (2 * j - 2) :=
    Nat.choose_mul (by omega)
  rw [choose_two_of_two_mul] at hid
  have h1 : 2 ^ e ∣ r.choose (2 * j) * j * (2 * j - 1) := by
    rw [mul_assoc, hid]
    exact Dvd.dvd.mul_right he _
  have hcop : Nat.Coprime (2 ^ e) (2 * j - 1) := by
    refine Nat.Coprime.pow_left _ ?_
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  exact hcop.dvd_of_dvd_mul_right h1

/-- The `2`-adic estimate for the terms of index `≥ 2` in the binomial expansion. -/
