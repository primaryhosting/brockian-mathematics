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


theorem integral_res_quad_path (hρ : ρ.PosDef) (hσ : σ.PosDef) (htr : ρ.trace = σ.trace)
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    (∫ t in Ioi (0:ℝ),
        (ρ * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re)
      = (1 - s) * bkm (pathState ρ σ s) (ρ - σ) := by
  have hω : (pathState ρ σ s).PosDef := pathState_posDef hρ hσ h0 h1
  have hΔ : (ρ - σ).IsHermitian := hρ.isHermitian.sub hσ.isHermitian
  have hρeq : ρ = pathState ρ σ s + ((1 - s : ℝ) : ℂ) • (ρ - σ) := by
    rw [pathState]
    push_cast
    module
  have hsplit : ∀ t ∈ Ioi (0:ℝ),
      (ρ * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re
        = (pathState ρ σ s * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re
          + (1 - s) * ((ρ - σ) * res (pathState ρ σ s) t * (ρ - σ)
              * res (pathState ρ σ s) t).trace.re := by
    intro t _
    have hmat : ρ * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t
        = (pathState ρ σ s * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t)
          + ((1 - s : ℝ) : ℂ) • ((ρ - σ) * res (pathState ρ σ s) t * (ρ - σ)
              * res (pathState ρ σ s) t) := by
      conv_lhs => rw [hρeq]
      simp [Matrix.add_mul, Matrix.smul_mul]
    rw [hmat, Matrix.trace_add, Matrix.trace_smul, Complex.add_re, smul_eq_mul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hsplit,
    MeasureTheory.integral_add (integrableOn_omega_res_quad hω (ρ - σ))
      ((integrableOn_res_quad hω hΔ).const_mul _),
    integral_omega_res_quad hω, MeasureTheory.integral_const_mul]
  have htr0 : ((ρ - σ).trace).re = 0 := by
    rw [Matrix.trace_sub, htr]
    simp
  rw [htr0, zero_add, bkm]

/-- Joint integrability of the two-parameter family of resolvent traces. -/
