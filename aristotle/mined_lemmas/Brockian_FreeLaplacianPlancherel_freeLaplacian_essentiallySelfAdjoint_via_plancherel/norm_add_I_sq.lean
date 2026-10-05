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

theorem norm_add_I_sq (hsym : ∀ x y : D, ⟪T x, (y : H)⟫ = ⟪(x : H), T y⟫) (x : D) :
    ‖T x + Complex.I • (x : H)‖ ^ 2 = ‖T x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
  have h2 : (starRingEnd ℂ) ⟪T x, (x : H)⟫ = ⟪T x, (x : H)⟫ := by
    rw [inner_conj_symm]; exact (hsym x x).symm
  rw [norm_add_pow_two (𝕜 := ℂ), inner_smul_right]
  have hre : RCLike.re (Complex.I * ⟪T x, (x : H)⟫) = 0 := by
    have him : (⟪T x, (x : H)⟫).im = 0 := Complex.conj_eq_iff_im.mp h2
    simp [him]
  rw [hre]
  simp [norm_smul]

/-- **Basic criterion for essential self-adjointness**: a densely defined symmetric operator
whose ranges `Ran(T + i)` and `Ran(T - i)` are both dense is essentially self-adjoint. -/
