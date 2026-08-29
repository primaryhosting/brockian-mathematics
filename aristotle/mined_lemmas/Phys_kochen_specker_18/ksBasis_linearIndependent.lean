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

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set,
recorded with integer entries. -/

theorem ksBasis_linearIndependent (j : Fin 9) :
    LinearIndependent ℝ (fun k : Fin 4 => ksVecE (ksBasis j k)) := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro k h
    exact ksVec_ne_zero (ksBasis j k) (congrArg WithLp.ofLp h)
  · intro k l hkl
    simp only [ksVecE, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    simpa [mul_comm] using ksBasis_orthogonal j k l hkl

/-- Each of the 9 quadruples spans `ℝ⁴`, hence is an orthogonal basis. -/
