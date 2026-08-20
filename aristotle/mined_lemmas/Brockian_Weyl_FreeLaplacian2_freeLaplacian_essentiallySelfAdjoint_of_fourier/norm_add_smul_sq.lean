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
# The basic criterion for essential self-adjointness

This file develops the abstract operator-theoretic input for `Brockian.Weyl.FreeLaplacian2`:
a densely defined symmetric operator on a complex Hilbert space whose two deficiency ranges
`Ran (T + i)` and `Ran (T - i)` are dense has self-adjoint closure, i.e. it is
*essentially self-adjoint*.
-/

namespace Brockian.Weyl

open LinearPMap Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator `x ↦ T x + z • x` on the domain of `T`. -/

theorem norm_add_smul_sq {T : H →ₗ.[ℂ] H} (hsymm : T.IsFormalAdjoint T) (x : T.domain) (z : ℂ)
    (hz : z.re = 0) : ‖T x + z • (x : H)‖ ^ 2 = ‖T x‖ ^ 2 + ‖z‖ ^ 2 * ‖(x : H)‖ ^ 2 := by
  have hreal : (starRingEnd ℂ) (inner ℂ (T x) (x : H)) = inner ℂ (T x) (x : H) := by
    rw [inner_conj_symm]; exact (hsymm x x).symm
  have hre : ((inner ℂ (T x) (x : H)) : ℂ).im = 0 := Complex.conj_eq_iff_im.mp hreal
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
  have h0 : (z * inner ℂ (T x) (x : H)).re = 0 := by rw [Complex.mul_re, hz, hre]; ring
  simp only [RCLike.re_to_complex, h0]
  rw [mul_pow]; ring

/-- If `T` is closed and symmetric, then its deficiency ranges (for unimodular purely imaginary
`z`) are closed. -/
