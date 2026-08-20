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

open MeasureTheory Complex
open scoped Real ComplexInnerProductSpace

noncomputable section

namespace Brockian.FreeLaplacianPlancherel

/-! ## Essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A densely defined symmetric operator `T` with domain `D` in a complex Hilbert space is
*essentially self-adjoint* when both deficiency spaces are trivial, i.e. when the ranges of
`T + i` and `T - i` are dense. -/

lemma eq_zero_of_weighted_inner_eq_zero {u : X → ℝ} (z w : Lp ℂ 2 μ)
    (hu : ∀ x, 0 < u x) (hw : ⇑w =ᵐ[μ] fun x => (u x : ℂ) * z x)
    (h : ⟪w, z⟫ = 0) : z = 0 := by
  have hint : Integrable (fun x => (inner ℂ (w x) (z x) : ℂ)) μ := L2.integrable_inner w z
  have heq : (fun x => (inner ℂ (w x) (z x) : ℂ))
      =ᵐ[μ] fun x => ((u x * ‖z x‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [hw] with x hx
    rw [hx, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    have hcomm : z x * ((u x : ℂ) * (starRingEnd ℂ) (z x))
        = (u x : ℂ) * (z x * (starRingEnd ℂ) (z x)) := by ring
    rw [hcomm, Complex.mul_conj']
    push_cast
    ring
  have hGint : Integrable (fun x => u x * ‖z x‖ ^ 2) μ := by
    have h' := (hint.congr heq).re
    simpa only [Complex.ofReal_re] using h'
  have hGzero : ∫ x, u x * ‖z x‖ ^ 2 ∂μ = 0 := by
    have h1 : ∫ x, ((u x * ‖z x‖ ^ 2 : ℝ) : ℂ) ∂μ = 0 := by
      rw [← integral_congr_ae heq, ← L2.inner_def]
      exact h
    rw [integral_complex_ofReal] at h1
    exact_mod_cast h1
  have hnonneg : 0 ≤ fun x => u x * ‖z x‖ ^ 2 := by
    intro x
    have := (hu x).le
    positivity
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg hGint).mp hGzero
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hae] with x hx
  have hx' : u x * ‖z x‖ ^ 2 = 0 := hx
  rcases mul_eq_zero.mp hx' with h' | h'
  · exact absurd h' (ne_of_gt (hu x))
  · have hzx : ‖z x‖ = 0 := by nlinarith [norm_nonneg (z x)]
    simpa using hzx

end Aux

/-- A real measurable function, viewed as a complex-valued a.e.-equivalence class. -/
