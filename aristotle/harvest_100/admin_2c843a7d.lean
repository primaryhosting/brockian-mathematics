/-!
# Triplet Two Patterns
Category: Cone Line
Target: Brockian.ConeLine.triplet_two_patterns
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option grind.warning false

namespace Brockian
namespace ConeLine

/-- A prime `q > 5` is not divisible by `5`. -/
lemma not_dvd_five_of_prime_gt_five {q : ℕ} (hq : Nat.Prime q) (h5 : 5 < q) : q % 5 ≠ 0 := by
  intro h
  have hdvd : (5 : ℕ) ∣ q := Nat.dvd_of_mod_eq_zero h
  have := (Nat.Prime.eq_one_or_self_of_dvd hq 5 hdvd)
  omega

/-- A prime triplet `(p, p+2, p+6)` with `p > 5` has exactly two possible ray patterns
modulo `5`: `(1,3,2)` or `(2,4,3)`. -/
theorem triplet_two_patterns {p : ℕ} (hp : Nat.Prime p) (hp2 : Nat.Prime (p + 2))
    (hp6 : Nat.Prime (p + 6)) (h5 : 5 < p) :
    (p % 5 = 1 ∧ (p + 2) % 5 = 3 ∧ (p + 6) % 5 = 2) ∨
      (p % 5 = 2 ∧ (p + 2) % 5 = 4 ∧ (p + 6) % 5 = 3) := by
  have h0 : p % 5 ≠ 0 := not_dvd_five_of_prime_gt_five hp h5
  have h2 : (p + 2) % 5 ≠ 0 := not_dvd_five_of_prime_gt_five hp2 (by omega)
  have h6 : (p + 6) % 5 ≠ 0 := not_dvd_five_of_prime_gt_five hp6 (by omega)
  omega

end ConeLine
end Brockian

