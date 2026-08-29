/-
# Quadruplet Visits All Active Rays
Category: Cone Line
Target: Brockian.ConeLine.quadruplet_visits_all_active_rays
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib


set_option autoImplicit false

namespace Brockian.ConeLine

/-- A prime greater than `5` is not divisible by `5`, i.e. its residue mod `5` is nonzero. -/

theorem quadruplet_visits_all_active_rays {p : ℕ} (hp : Nat.Prime p)
    (hp2 : Nat.Prime (p + 2)) (hp6 : Nat.Prime (p + 6)) (hp8 : Nat.Prime (p + 8))
    (h5 : 5 < p) :
    p % 5 = 1 ∧ (p + 2) % 5 = 3 ∧ (p + 6) % 5 = 2 ∧ (p + 8) % 5 = 4 := by
  have h0 := mod_five_ne_zero_of_prime hp h5
  have h2 := mod_five_ne_zero_of_prime hp2 (by omega)
  have h6 := mod_five_ne_zero_of_prime hp6 (by omega)
  have h8 := mod_five_ne_zero_of_prime hp8 (by omega)
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

