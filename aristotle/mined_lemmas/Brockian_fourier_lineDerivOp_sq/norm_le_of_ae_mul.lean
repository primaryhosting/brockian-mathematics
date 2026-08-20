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
# The Fourier transform of the Laplacian on Schwartz space

We record the classical formula `𝓕 (Δ f) ξ = -(4π²‖ξ‖²) 𝓕 f ξ` for Schwartz functions,
introduce the Fourier symbol `freeSymbol ξ = 4π²‖ξ‖²` of the free Laplacian `-Δ`, and show that
the "resolvent multiplier" `ξ ↦ (1 + freeSymbol ξ)⁻¹` has temperate growth (so that multiplying
a Schwartz function by it produces again a Schwartz function).
-/

namespace Brockian

open MeasureTheory SchwartzMap Real LineDeriv
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


theorem norm_le_of_ae_mul {C : ℝ} (hC : 0 ≤ C) {b : V → ℂ} {u w : L2 V}
    (hb : ∀ᵐ x ∂(volume : Measure V), ‖b x‖ ≤ C)
    (h : (w : V → ℂ) =ᵐ[volume] fun x => b x * (u : V → ℂ) x) : ‖w‖ ≤ C * ‖u‖ := by
  have h2 : ∀ᵐ x ∂(volume : Measure V),
      ‖(w : V → ℂ) x‖ ≤ ‖((C : ℝ) • u : L2 V) x‖ := by
    filter_upwards [h, hb, Lp.coeFn_smul (C : ℝ) u] with x hx hbx hsx
    rw [hx, hsx]
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC, norm_mul]
    exact mul_le_mul_of_nonneg_right hbx (norm_nonneg _)
  have := MeasureTheory.Lp.norm_le_norm_of_ae_le h2
  simpa [norm_smul, abs_of_nonneg hC] using this

section mul

variable (m : V → ℝ)

/-- The maximal domain of the multiplication operator by `m` inside `L²`. -/
