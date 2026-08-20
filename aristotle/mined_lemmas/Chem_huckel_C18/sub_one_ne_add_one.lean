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

set_option grind.warning false

namespace Chem

open Matrix

/-- The standard additive character `x ↦ exp (2 π i x / 18)` on `ZMod 18`. -/

lemma sub_one_ne_add_one (j : ZMod 18) : j - 1 ≠ j + 1 := by
  intro h
  have h2 : (2 : ZMod 18) = 0 := by linear_combination (norm := ring_nf) -h
  exact absurd h2 (by decide)

