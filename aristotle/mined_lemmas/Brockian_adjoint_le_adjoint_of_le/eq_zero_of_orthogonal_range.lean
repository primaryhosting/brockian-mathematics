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

theorem eq_zero_of_orthogonal_range (d : ℕ) (z : ℂ) (hz : z.im ≠ 0) (u : L2s d)
    (hu : ∀ f : 𝓢(EuclSpace d, ℂ),
      ⟪u, schwartzToL2 d (-(Δ f)) + z • schwartzToL2 d f⟫ = 0) :
    u = 0 := by
  have hv : (𝓕 u : L2s d) = 0 := by
    refine eq_zero_of_integral_eq_zero d (𝓕 u)
      (fun ξ => (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) + z) (by fun_prop) ?_
      (integral_symbol_eq_zero d z u hu)
    intro ξ hξ
    apply hz
    have hξ' : (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) + z = 0 := hξ
    have h0 : (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ).im + z.im = 0 := by
      rw [← Complex.add_im, hξ', Complex.zero_im]
    rwa [Complex.ofReal_im, zero_add] at h0
  have hv' : (MeasureTheory.Lp.fourierTransformₗᵢ (EuclSpace d) ℂ) u = 0 := hv
  exact (LinearIsometryEquiv.map_eq_zero_iff _).mp hv'

/-! ### The main theorem -/

/-- **The free Laplacian is essentially self-adjoint.**

The operator `-Δ` on `L²(ℝ^d, ℂ)`, with domain the image of the Schwartz space, is densely
defined and symmetric, its adjoint is self-adjoint (that is: `-Δ` is essentially
self-adjoint), and `(-Δ)†` is its unique self-adjoint extension.

The proof of the range condition in von Neumann's criterion goes through Plancherel's theorem:
the Fourier transform is unitary on `L²` and conjugates `-Δ` into multiplication by the
nowhere vanishing symbol `4π²‖ξ‖² ± i`. -/
