/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
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

set_option grind.warning false

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set in `ℝ⁴`. -/

theorem ksCtx_linearIndependent (c : Fin 9) :
    LinearIndependent ℝ (fun i : Fin 4 => ksVec (ksCtx c i)) :=
  linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => ksVec_ne_zero (ksCtx c i))
    (fun i j hij => ksCtx_orthogonal c i j hij)

/-- Each context is in fact an orthogonal basis of `ℝ⁴`: its four vectors span the space. -/
