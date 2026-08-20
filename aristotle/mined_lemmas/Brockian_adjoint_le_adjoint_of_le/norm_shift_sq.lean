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
# A basic criterion for essential self-adjointness

This file develops, from scratch, the classical criterion of von Neumann:

If `A` is a densely defined symmetric operator on a complex Hilbert space `H` such that the
ranges of `A + i` and `A - i` are dense — stated here in the equivalent form that a vector
orthogonal to such a range vanishes — then the adjoint `A†` is self-adjoint.  This is exactly
the statement that `A` is *essentially self-adjoint*: the closure of `A` (which is `A††`) is
self-adjoint, equivalently `A` has a unique self-adjoint extension, namely `A†`.

## Main results

* `Brockian.isSelfAdjoint_adjoint_of_denseRange`: the criterion.
* `Brockian.eq_adjoint_of_isSelfAdjoint_of_le`: uniqueness of the self-adjoint extension.
-/

open scoped ComplexInnerProductSpace
open LinearPMap

noncomputable section

namespace Brockian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Antitonicity of the adjoint: an extension has a smaller adjoint. -/

theorem norm_shift_sq {B : H →ₗ.[ℂ] H}
    (hsym : ∀ x y : B.domain, ⟪B x, (y : H)⟫ = ⟪(x : H), B y⟫) {z : ℂ} (hre : z.re = 0)
    (hnorm : ‖z‖ = 1) (x : B.domain) :
    ‖B x + z • (x : H)‖ ^ 2 = ‖B x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
  have hr : ⟪B x, (x : H)⟫ = ((⟪B x, (x : H)⟫.re : ℝ) : ℂ) := by
    have h2 : ⟪B x, (x : H)⟫ = (starRingEnd ℂ) ⟪B x, (x : H)⟫ := by
      rw [inner_conj_symm]; exact hsym x x
    exact (Complex.conj_eq_iff_re.mp h2.symm).symm
  rw [@norm_add_sq ℂ, inner_smul_right, hr]
  simp [hre, norm_smul, hnorm]

/-- The range of `B + z` is closed, for `B` closed and satisfying the Pythagoras identity. -/
