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
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem hasDerivAt_res_path (hρ : ρ.PosDef) (hσ : σ.PosDef) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun u : ℝ => res (pathState ρ σ u) t)
      (-(res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t)) s := by
  have hunit : IsUnit ((σ + (t : ℂ) • 1) + (s : ℂ) • (ρ - σ)) := by
    rw [shift_pathState_eq]
    exact (posDef_shift (pathState_posDef hρ hσ h0 h1) ht).isUnit
  have := hasDerivAt_inv_affine (σ + (t : ℂ) • 1) (ρ - σ) hunit
  simpa only [← res_pathState_eq] using this

/-- The derivative of `s ↦ -Tr (A (ω s + t)⁻¹)` along the path. -/
