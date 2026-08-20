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

theorem freeLaplacianPMap_apply (d : ℕ) (x : (freeLaplacianPMap d).domain)
    (f : 𝓢(EuclSpace d, ℂ)) (hx : schwartzToL2 d f = (x : L2s d)) :
    freeLaplacianPMap d x = schwartzToL2 d (-(Δ f)) := by
  have hxe : (LinearEquiv.ofInjective (schwartzToL2 d) (schwartzToL2_injective d)).symm x = f := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext hx.symm
  refine Eq.trans (congrArg (⇑(schwartzToL2 d ∘ₗ negLaplacianL d)) hxe) ?_
  rw [LinearMap.comp_apply, negLaplacianL_apply]

/-! ### The Fourier transform of the Laplacian -/

/-- The Fourier transform turns a line derivative into multiplication by `2πi⟪ξ, m⟫`. -/
