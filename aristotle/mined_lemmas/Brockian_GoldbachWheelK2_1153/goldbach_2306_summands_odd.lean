/-
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

/-- Key intermediate lemma: the wheel partner `2293 = 2 * 1153 - 13` is prime. -/

lemma goldbach_2306_summands_odd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p + q = 2 * 1153) : Odd p ∧ Odd q := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : q = 2304 := by omega
    subst this
    exact absurd hq (by norm_num)
  have hq2 : q ≠ 2 := by
    rintro rfl
    have : p = 2304 := by omega
    subst this
    exact absurd hp (by norm_num)
  exact ⟨hp.odd_of_ne_two hp2, hq.odd_of_ne_two hq2⟩

end Brockian

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

