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

theorem eq_zero_of_integral_eq_zero (d : ℕ) (v : L2s d) (ψ : EuclSpace d → ℂ)
    (hψc : Continuous ψ) (hψ : ∀ ξ, ψ ξ ≠ 0)
    (hE : ∀ g : 𝓢(EuclSpace d, ℂ), ∫ ξ, conj ((v : EuclSpace d → ℂ) ξ) * ψ ξ * g ξ = 0) :
    v = 0 := by
  set w : EuclSpace d → ℂ := fun ξ => conj ((v : EuclSpace d → ℂ) ξ) * ψ ξ with hw
  have hloc : LocallyIntegrable w volume := by
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    have h0 : IntegrableOn (fun ξ => (v : EuclSpace d → ℂ) ξ) K volume :=
      ((Lp.memLp v).locallyIntegrable (by norm_num)).integrableOn_isCompact hK
    have h1 : IntegrableOn (fun ξ => conj ((v : EuclSpace d → ℂ) ξ)) K volume :=
      (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap).integrable_comp h0
    exact h1.mul_continuousOn hψc.continuousOn hK
  have hzero : ∀ᵐ ξ, w ξ = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    intro g g_smooth g_cpt
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hg₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) (Complex.ofRealCLM ∘ g) := by fun_prop
    have hE' := hE (hg₁.toSchwartzMap hg₂)
    rw [← hE']
    apply integral_congr_ae
    filter_upwards with ξ
    have hcoe : (hg₁.toSchwartzMap hg₂ : EuclSpace d → ℂ) ξ = (g ξ : ℂ) := rfl
    rw [hcoe, hw]
    simp [Complex.real_smul]
    ring
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hzero] with ξ hξ
  rcases mul_eq_zero.mp hξ with h | h
  · simpa using congrArg (starRingEnd ℂ) h
  · exact absurd h (hψ ξ)

/-- The range of `-Δ + z` (on Schwartz functions) has trivial orthogonal complement, for any
non-real `z`. -/
