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

Let `T` be a densely defined symmetric operator on a complex Hilbert space `H`.
If the ranges of `T + i` and `T - i` are both dense, then the adjoint `T†` is
self-adjoint, i.e. `T` is essentially self-adjoint.

Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open LinearPMap MeasureTheory Filter Topology

namespace Brockian.Weyl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The range of `T + z` for a partially defined operator `T` and a scalar `z`. -/

theorem exists_schwartz_neg_deriv_two_add_smul {z : ℂ} (hz : z.im ≠ 0) (h : 𝓢(ℝ, ℂ)) :
    ∃ u : 𝓢(ℝ, ℂ), -(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ u)) + z • u = h := by
  have hfd : ∀ (f : 𝓢(ℝ, ℂ)) (ξ : ℝ),
      (𝓕 (SchwartzMap.derivCLM ℂ ℂ f)) ξ = (2 * Real.pi * Complex.I * ξ) * (𝓕 f) ξ := by
    intro f ξ
    have hd : ⇑(SchwartzMap.derivCLM ℂ ℂ f) = deriv (⇑f) := by
      ext x; simp [SchwartzMap.derivCLM_apply]
    rw [SchwartzMap.fourier_coe, hd, Real.fourier_deriv f.integrable f.differentiable
      (by rw [← hd]; exact (SchwartzMap.derivCLM ℂ ℂ f).integrable)]
    simp [SchwartzMap.fourier_coe]
  set m : ℝ → ℂ := fun ξ => (((4 * Real.pi ^ 2 * ξ ^ 2 : ℝ) : ℂ) + z)⁻¹ with hm
  have hmtg : Function.HasTemperateGrowth m :=
    (hasTemperateGrowth_inv_ofReal_add hz).comp (by fun_prop)
  refine ⟨𝓕⁻ (SchwartzMap.smulLeftCLM ℂ m (𝓕 h)), ?_⟩
  set u : 𝓢(ℝ, ℂ) := 𝓕⁻ (SchwartzMap.smulLeftCLM ℂ m (𝓕 h)) with hu
  have hFu : 𝓕 u = SchwartzMap.smulLeftCLM ℂ m (𝓕 h) := FourierTransform.fourier_fourierInv_eq _
  have hinj : ∀ a b : 𝓢(ℝ, ℂ), 𝓕 a = 𝓕 b → a = b := by
    intro a b hab
    have ha : (𝓕⁻ (𝓕 a) : 𝓢(ℝ, ℂ)) = a := FourierTransform.fourierInv_fourier_eq a
    have hb : (𝓕⁻ (𝓕 b) : 𝓢(ℝ, ℂ)) = b := FourierTransform.fourierInv_fourier_eq b
    rw [← ha, ← hb, hab]
  apply hinj
  have hlin : 𝓕 (-(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ u)) + z • u)
      = -(𝓕 (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ u))) + z • 𝓕 u := by
    show SchwartzMap.fourierTransformCLM ℂ _ = _
    rw [map_add, map_neg, map_smul]
    rfl
  rw [hlin]
  ext ξ
  have h1 : (𝓕 (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ u))) ξ
      = (2 * Real.pi * Complex.I * ξ) * ((2 * Real.pi * Complex.I * ξ) * (𝓕 u) ξ) := by
    rw [hfd, hfd]
  have h2 : (𝓕 u) ξ = m ξ * (𝓕 h) ξ := by
    rw [hFu, SchwartzMap.smulLeftCLM_apply_apply hmtg]
    simp
  have hne : (((4 * Real.pi ^ 2 * ξ ^ 2 : ℝ) : ℂ) + z) ≠ 0 := by
    intro hc
    apply hz
    have := congrArg Complex.im hc
    rw [Complex.add_im, Complex.ofReal_im, zero_add, Complex.zero_im] at this
    exact this
  simp only [SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply, h1, h2, hm,
    smul_eq_mul]
  field_simp
  rw [Complex.I_sq]
  push_cast
  ring

end Brockian.Weyl

import Mathlib
import Brockian.Weyl.EssentialSelfAdjointness
import Brockian.Weyl.SchwartzResolvent

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap Complex LinearPMap
open scoped SchwartzMap FourierTransform

namespace Brockian.Weyl.FreeLaplacian2

/-- The complex Hilbert space `L²(ℝ)`. -/
abbrev L2R : Type := Lp ℂ 2 (volume : Measure ℝ)

/-- The inclusion of the Schwartz space into `L²(ℝ)`. -/
