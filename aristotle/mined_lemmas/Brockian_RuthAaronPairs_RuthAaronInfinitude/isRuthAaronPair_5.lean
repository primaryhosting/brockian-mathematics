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

/-
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.RuthAaronPairs

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(so `sopfr 12 = 2 + 2 + 3 = 7`).  By convention `sopfr 0 = sopfr 1 = 0`. -/

theorem isRuthAaronPair_5 : IsRuthAaronPair 5 := by
  refine ⟨by norm_num, ?_⟩
  have h5 : sopfr 5 = 5 := sopfr_prime (by norm_num)
  have h6 : sopfr (5 + 1) = 5 := by
    have h : (5 : ℕ) + 1 = 2 * 3 := by norm_num
    rw [h, sopfr_mul (by norm_num) (by norm_num), sopfr_prime (by norm_num),
      sopfr_prime (by norm_num)]
  rw [h5, h6]

/-! ### Reduction: infinitude is equivalent to unboundedness -/

/-- The set of Ruth–Aaron pairs is infinite exactly when it is unbounded, i.e. when Ruth–Aaron
pairs occur beyond every bound. -/
