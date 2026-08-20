import Brockian.Weyl.FreeLaplacian2

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
Essential self-adjointness of the free Laplacian on `L²(ℝᵈ)`, via the Fourier transform.
-/
import Mathlib

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Real Function LineDeriv
open scoped FourierTransform ComplexInnerProductSpace Laplacian LinearPMap ContDiff

noncomputable section

variable (d : ℕ)

/-- The configuration space `ℝᵈ`. -/
abbrev EuclSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝᵈ, ℂ)`. -/
abbrev L2 (d : ℕ) := Lp (α := EuclSpace d) ℂ 2

/-- The symbol of the free Laplacian: `-Δ` acts on the Fourier side as multiplication by
`4π²‖ξ‖²`. -/

theorem freeLaplacian_isFormalAdjoint_self :
    (freeLaplacian d).IsFormalAdjoint (freeLaplacian d) := by
  intro x y
  obtain ⟨φ, rfl⟩ := exists_schwartz_of_mem_domain x
  obtain ⟨ψ, rfl⟩ := exists_schwartz_of_mem_domain y
  rw [freeLaplacian_apply_toLp, freeLaplacian_apply_toLp]
  simp only [SchwartzMap.inner_toL2_toL2_eq, negLaplacianCLM_apply, RCLike.inner_apply']
  have hIBP := SchwartzMap.integral_bilinear_laplacian_right_eq_left
    (μ := (volume : Measure (EuclSpace d))) φ ψ
    ((ContinuousLinearMap.mul ℝ ℂ).comp (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, ContinuousLinearMap.mul_apply'] at hIBP
  simp only [SchwartzMap.neg_apply, map_neg, neg_mul, mul_neg, integral_neg]
  rw [hIBP]

/-! ### The adjoint -/

/-- The Fourier transform of an element of the domain of the adjoint gets multiplied by the
symbol. -/
