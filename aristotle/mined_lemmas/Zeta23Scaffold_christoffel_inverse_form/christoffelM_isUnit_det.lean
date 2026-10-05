/-
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Scaffold

/-- The order-3 sine-kernel Hankel matrix. -/

theorem christoffelM_isUnit_det : IsUnit christoffelM.det := by
  rw [christoffelM_det]
  exact isUnit_iff_ne_zero.2 (by norm_num)

/-- The `(0,0)` entry of the inverse Hankel matrix is `36/5`. -/
