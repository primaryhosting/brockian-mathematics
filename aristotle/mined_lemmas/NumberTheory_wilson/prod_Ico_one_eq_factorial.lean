/-
# Wilson
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.wilson
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

namespace NumberTheory

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- `(p - 1)!` is the product of the integers `1, 2, …, p - 1`. -/

theorem prod_Ico_one_eq_factorial : (∏ x ∈ Finset.Ico 1 p, x) = (p - 1)! := by
  conv_lhs => rw [← Nat.succ_pred_eq_of_pos (Fact.out : Nat.Prime p).pos]
  exact Finset.prod_Ico_id_eq_factorial _

/-- Key intermediate step: the product of the nonzero residues `1, 2, …, p - 1`
modulo a prime `p` equals `-1` in `ZMod p`. -/
