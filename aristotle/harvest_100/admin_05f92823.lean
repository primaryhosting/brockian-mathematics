/-
# Triplet Two Patterns
Category: Cone Line
Target: Brockian.ConeLine.triplet_two_patterns
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.ConeLine

/-- A prime triplet `(p, p+2, p+6)` with `p > 5` has exactly two possible
residue patterns mod 5: `(1, 3, 2)` or `(2, 4, 3)`. -/
theorem triplet_two_patterns (p : ℕ) (hp : Nat.Prime p) (hp2 : Nat.Prime (p + 2))
    (hp6 : Nat.Prime (p + 6)) (h5 : 5 < p) :
    (p % 5 = 1 ∧ (p + 2) % 5 = 3 ∧ (p + 6) % 5 = 2) ∨
    (p % 5 = 2 ∧ (p + 2) % 5 = 4 ∧ (p + 6) % 5 = 3) := by
  have h1 : ¬ (5 ∣ p) := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h; omega
  have h2 : ¬ (5 ∣ (p + 2)) := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp2).mp h; omega
  have h3 : ¬ (5 ∣ (p + 6)) := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp6).mp h; omega
  rw [Nat.dvd_iff_mod_eq_zero] at h1 h2 h3
  omega

#print axioms Brockian.ConeLine.triplet_two_patterns

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

