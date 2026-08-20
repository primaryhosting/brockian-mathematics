/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The commutator `[H, A] = H A - A H` of two continuous linear operators. -/

theorem ehrenfest_stationary (hbar E0 : ℝ) (H : E →L[ℂ] E)
    (hH : ∀ x y : E, ⟪H x, y⟫_ℂ = ⟪x, H y⟫_ℂ) (v : E) (hv : H v = (E0 : ℂ) • v)
    (B : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (fun s => ⟪stationaryState hbar E0 v s, B (stationaryState hbar E0 v s)⟫_ℂ) 0 t := by
  set psi := stationaryState hbar E0 v with hpsidef
  have hpsi := hasDerivAt_stationaryState hbar E0 H v hv t
  have key := ehrenfest hbar H hH psi (fun _ => B) 0 t hpsi (hasDerivAt_const t B)
  refine key.congr_deriv ?_
  have hHpsi : H (psi t) = (E0 : ℂ) • psi t := by
    rw [hpsidef]
    simp only [stationaryState, ContinuousLinearMap.map_smul, hv]
    rw [smul_comm]
  have h1 : ⟪psi t, H (B (psi t))⟫_ℂ = (E0 : ℂ) * ⟪psi t, B (psi t)⟫_ℂ := by
    rw [← hH (psi t) (B (psi t)), hHpsi, inner_smul_left]
    simp
  have h2 : ⟪psi t, B (H (psi t))⟫_ℂ = (E0 : ℂ) * ⟪psi t, B (psi t)⟫_ℂ := by
    rw [hHpsi]
    simp
  simp only [commutator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, inner_sub_right, h1, h2]
  simp

end QPhys

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

