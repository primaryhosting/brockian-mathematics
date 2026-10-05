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

lemma two_ne_zero_of_dvd {p r : ℕ} (hr : r.Prime) (hrq : r ∣ 2 * p + 1) :
    (2 : ZMod r) ≠ 0 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    omega
  intro h
  have hc : ((2 : ℕ) : ZMod r) = 0 := by push_cast; exact h
  have hdvd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp hc
  have := Nat.le_of_dvd (by norm_num) hdvd
  have := hr.two_le
  omega

/-- If a prime `r` divides `2 * p + 1` and the order of `2` modulo `r` is `p`,
then `r = 2 * p + 1`. -/
