/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module doc-comment `/-! ... -/` before `import`,
-- so the required header appears above as an ordinary block comment.)

import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QI

/-! ## Elementary trigonometric estimates -/

/-- A crude but explicit linear lower bound for `sin` on `[0, 5π/8]`. -/

theorem lt_Acnt_iff {Q r x0 : ℕ} (hr : 0 < r) (j : ℕ) :
    j < Acnt Q r x0 ↔ x0 + j * r < Q := by
  unfold Acnt
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hr, add_mul, one_mul]
  omega

