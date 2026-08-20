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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Triplet Two Patterns
Category: Cone Line
Target: Brockian.ConeLine.triplet_two_patterns
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Brockian.ConeLine

/-- A prime `q > 5` is not divisible by `5`. -/
theorem not_dvd_five_of_prime_gt_five {q : ℕ} (hq : q.Prime) (h : 5 < q) : ¬ (5 ∣ q) := by
  intro hdvd
  have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp hdvd
  omega

/-- A prime triplet `(p, p+2, p+6)` with `p > 5` has exactly two possible ray patterns
modulo `5`: `(1, 3, 2)` or `(2, 4, 3)`. -/
theorem triplet_two_patterns {p : ℕ} (hp : p.Prime) (hp2 : (p + 2).Prime)
    (hp6 : (p + 6).Prime) (h5 : 5 < p) :
    (p % 5 = 1 ∧ (p + 2) % 5 = 3 ∧ (p + 6) % 5 = 2) ∨
    (p % 5 = 2 ∧ (p + 2) % 5 = 4 ∧ (p + 6) % 5 = 3) := by
  have h0 : ¬ (5 ∣ p) := not_dvd_five_of_prime_gt_five hp h5
  have h1 : ¬ (5 ∣ (p + 2)) := not_dvd_five_of_prime_gt_five hp2 (by omega)
  have h2 : ¬ (5 ∣ (p + 6)) := not_dvd_five_of_prime_gt_five hp6 (by omega)
  rw [Nat.dvd_iff_mod_eq_zero] at h0 h1 h2
  omega

end Brockian.ConeLine

