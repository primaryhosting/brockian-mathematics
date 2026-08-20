/-
# Quadruplet Visits All Active Rays
Category: Cone Line
Target: Brockian.ConeLine.quadruplet_visits_all_active_rays
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.ConeLine

/-- A prime `q > 5` is not divisible by `5`. -/
lemma not_dvd_five_of_prime_gt_five {q : ℕ} (hq : q.Prime) (h : 5 < q) : q % 5 ≠ 0 := by
  intro h0
  have : (5 : ℕ) ∣ q := Nat.dvd_of_mod_eq_zero h0
  have := (Nat.Prime.eq_one_or_self_of_dvd hq 5 this)
  omega

/-- A prime quadruplet `(p, p+2, p+6, p+8)` with `p > 5` has residues
`1, 3, 2, 4` modulo `5`, in that order. -/
theorem quadruplet_visits_all_active_rays {p : ℕ}
    (hp : p.Prime) (hp2 : (p + 2).Prime) (hp6 : (p + 6).Prime) (hp8 : (p + 8).Prime)
    (h5 : 5 < p) :
    p % 5 = 1 ∧ (p + 2) % 5 = 3 ∧ (p + 6) % 5 = 2 ∧ (p + 8) % 5 = 4 := by
  have h0 := not_dvd_five_of_prime_gt_five hp h5
  have h2 := not_dvd_five_of_prime_gt_five hp2 (by omega)
  have h6 := not_dvd_five_of_prime_gt_five hp6 (by omega)
  have h8 := not_dvd_five_of_prime_gt_five hp8 (by omega)
  omega

end Brockian.ConeLine

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

