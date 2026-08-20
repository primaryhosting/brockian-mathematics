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

theorem exists_schwartz_solution {z : ℂ} (hz : z.im ≠ 0) (ψ : 𝓢(V, ℂ))
    (hψ : HasCompactSupport ψ) : ∃ u : 𝓢(V, ℂ), -(Δ u) + z • u = 𝓕⁻ ψ := by
  classical
  set m : V → ℂ := fun ξ => ((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + z with hm
  have hm0 : ∀ ξ, m ξ ≠ 0 := by
    intro ξ h
    apply hz
    have h2 : (m ξ).im = z.im := by simp only [hm, Complex.add_im, Complex.ofReal_im, zero_add]
    rw [← h2, h, Complex.zero_im]
  have hmsmooth : ContDiff ℝ ∞ m := by
    have h1 : ContDiff ℝ ∞ (fun ξ : V => (4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) := by
      have := (contDiff_norm_sq (E := V) (n := ∞) ℝ)
      fun_prop
    have h2 : ContDiff ℝ ∞ (fun ξ : V => ((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp h1
    simp only [hm]
    exact h2.add contDiff_const
  have hsmooth : ContDiff ℝ ∞ (fun ξ => ψ ξ * (m ξ)⁻¹) :=
    (ψ.smooth ⊤).mul (hmsmooth.inv hm0)
  have hcs : HasCompactSupport (fun ξ => ψ ξ * (m ξ)⁻¹) := hψ.mul_right
  set φ : 𝓢(V, ℂ) := hcs.toSchwartzMap hsmooth with hφ
  refine ⟨𝓕⁻ φ, ?_⟩
  have hFw : 𝓕 (𝓕⁻ φ) = φ := fourier_fourierInv_eq φ
  have hF : 𝓕 (-(Δ (𝓕⁻ φ)) + z • (𝓕⁻ φ)) = ψ := by
    ext ξ
    have h1 : 𝓕 (-(Δ (𝓕⁻ φ)) + z • (𝓕⁻ φ)) = -(𝓕 (Δ (𝓕⁻ φ))) + z • 𝓕 (𝓕⁻ φ) := by simp
    rw [h1, SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply,
      fourier_laplacian_apply, hFw]
    have hφξ : φ ξ = ψ ξ * (m ξ)⁻¹ := by simp [hφ]
    have hmξ : m ξ = 4 * (π : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2 + z := by
      simp only [hm]; push_cast; ring
    have hne : 4 * (π : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2 + z ≠ 0 := by rw [← hmξ]; exact hm0 ξ
    rw [hφξ, hmξ, smul_eq_mul]
    field_simp
  calc -(Δ (𝓕⁻ φ)) + z • 𝓕⁻ φ = 𝓕⁻ (𝓕 (-(Δ (𝓕⁻ φ)) + z • 𝓕⁻ φ)) :=
        (fourierInv_fourier_eq _).symm
    _ = 𝓕⁻ ψ := by rw [hF]

variable (V)

/-! ### The free Laplacian as an unbounded operator on `L²` -/

/-- The Hilbert space `L²(V, ℂ)`. -/
abbrev L2Space := MeasureTheory.Lp (α := V) ℂ 2 volume

/-- The inclusion of the Schwartz space into `L²`. -/
