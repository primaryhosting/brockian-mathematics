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
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap ComplexInnerProductSpace FourierTransform Laplacian Real

namespace Brockian.FreeLaplacianPlancherel

noncomputable section

/-! ## An abstract criterion for essential self-adjointness

We work with a symmetric, densely defined operator `T` with domain a submodule `D` of a complex
Hilbert space `H`.  Mathlib does not (yet) have a theory of unbounded operators, so we spell out
the relevant notions.
-/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `IsAdjointPair D T y z` says that `y` belongs to the domain of the adjoint of the operator
`T` (with domain `D`) and that `z` is a corresponding adjoint value, i.e.
`⟪T x, y⟫ = ⟪x, z⟫` for all `x` in the domain.  If `D` is dense then `z` is uniquely determined
by `y`, and `z = T* y`. -/

theorem inner_toLp_laplacian (f g : 𝓢(V, ℂ)) :
    ⟪(Δ f).toLp 2 volume, g.toLp 2 volume⟫ = ⟪f.toLp 2 volume, (Δ g).toLp 2 volume⟫ := by
  rw [inner_toLp_toLp, inner_toLp_toLp]
  have := SchwartzMap.integral_bilinear_laplacian_right_eq_left (μ := (volume : Measure V)) f g
    ((ContinuousLinearMap.mul ℝ ℂ).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ))
  simpa using this.symm

/-! ### Density of the ranges, via Plancherel -/

/-- If `w ∈ L²` is such that `∫ conj((4π²‖ξ‖² + c) φ(ξ)) w(ξ) dξ = 0` for every Schwartz function
`φ`, and `4π²‖ξ‖² + c` never vanishes, then `w = 0`. -/
