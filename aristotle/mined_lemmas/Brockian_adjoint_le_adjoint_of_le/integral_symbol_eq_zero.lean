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

theorem integral_symbol_eq_zero (d : ℕ) (z : ℂ) (u : L2s d)
    (hu : ∀ f : 𝓢(EuclSpace d, ℂ),
      ⟪u, schwartzToL2 d (-(Δ f)) + z • schwartzToL2 d f⟫ = 0)
    (g : 𝓢(EuclSpace d, ℂ)) :
    ∫ ξ, conj (((𝓕 u : L2s d) : EuclSpace d → ℂ) ξ)
      * ((((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) + z) * g ξ = 0 := by
  set f : 𝓢(EuclSpace d, ℂ) := 𝓕⁻ g with hf
  have hfg : (𝓕 f : 𝓢(EuclSpace d, ℂ)) = g := FourierTransform.fourier_fourierInv_eq g
  set h : 𝓢(EuclSpace d, ℂ) := -(Δ f) + z • f with hh
  have h1 : schwartzToL2 d (-(Δ f)) + z • schwartzToL2 d f = schwartzToL2 d h := by
    rw [hh, map_add, map_smul]
  have h2 : ⟪u, schwartzToL2 d h⟫ = 0 := by rw [← h1]; exact hu f
  have h3 : ⟪(𝓕 u : L2s d), (𝓕 (schwartzToL2 d h) : L2s d)⟫ = 0 := by
    rw [MeasureTheory.Lp.inner_fourier_eq]; exact h2
  have h4 : (𝓕 (schwartzToL2 d h) : L2s d) = schwartzToL2 d (𝓕 h) := by
    rw [schwartzToL2_apply, SchwartzMap.toLp_fourier_eq]
    rfl
  rw [h4, inner_lp_schwartz] at h3
  rw [← h3]
  apply integral_congr_ae
  filter_upwards with ξ
  have hFT : ∀ p : 𝓢(EuclSpace d, ℂ), (𝓕 p : 𝓢(EuclSpace d, ℂ))
      = SchwartzMap.fourierTransformCLM ℂ p := fun _ => rfl
  have h5 : (𝓕 h : 𝓢(EuclSpace d, ℂ)) ξ
      = (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + z) * g ξ := by
    rw [hh, hFT, map_add, map_smul, map_neg]
    simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.neg_apply, smul_eq_mul,
      SchwartzMap.fourierTransformCLM_apply]
    rw [fourier_laplacian_apply, hfg]
    push_cast
    ring
  rw [h5]
  ring

/-- A vector of `L²` whose product with a nowhere vanishing continuous function integrates to
zero against every Schwartz function is zero. -/
