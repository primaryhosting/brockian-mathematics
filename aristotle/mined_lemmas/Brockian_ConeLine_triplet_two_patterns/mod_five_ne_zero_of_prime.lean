/-
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian.ConeLine

/-- A prime `q > 5` is not divisible by `5`. -/

lemma mod_five_ne_zero_of_prime {q : ℕ} (hq : Nat.Prime q) (h5 : 5 < q) : q % 5 ≠ 0 := by
  intro h
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq 5 (Nat.dvd_of_mod_eq_zero h)) with h' | h' <;>
    omega

/-- A prime triplet `(p, p+2, p+6)` with `p > 5` has exactly two possible ray patterns
modulo `5`: `(1, 3, 2)` or `(2, 4, 3)`. -/
