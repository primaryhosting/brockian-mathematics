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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a Sophie Germain prime if both `p` and `2 * p + 1` are prime. -/

lemma orderOf_two_ne_one {r : ℕ} (hr : r.Prime) : orderOf (2 : ZMod r) ≠ 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  intro h
  have h2 : (2 : ZMod r) = 1 := orderOf_eq_one_iff.mp h
  have hc : ((1 : ℕ) : ZMod r) = 0 := by push_cast; linear_combination h2
  have hdvd : r ∣ 1 := (ZMod.natCast_eq_zero_iff 1 r).mp hc
  have := Nat.le_of_dvd one_pos hdvd
  have := hr.two_le
  omega

/-- If `d` divides `2 * p` with `p` prime but `d` does not divide `p`, then `d = 2` or `d = 2 * p`. -/
