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

/-
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open MeasureTheory SchwartzMap FourierTransform Laplacian LineDeriv

noncomputable section

namespace Brockian.Weyl.FreeLaplacian2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The complex Hilbert space `L²(E)` of square integrable functions on a finite-dimensional
real inner product space `E`, with respect to the Lebesgue (Haar) measure. -/
abbrev L2Space (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] : Type _ := ↥(Lp (α := E) ℂ 2 volume)

/-- Schwartz functions viewed as elements of `L²(E)`. -/

theorem isFourierMul_of_pairing_adjoint (z w : L2Space E)
    (h : ∀ Y : (freeLaplacian (E := E)).adjoint.domain,
      inner ℂ w (Y : L2Space E) = inner ℂ z ((freeLaplacian (E := E)).adjoint Y)) :
    IsFourierMul z w := by
  have hZm : MemLp (fun ξ => ((𝓕 z : L2Space E) ξ)) 2 volume := Lp.memLp _
  have hWm : MemLp (fun ξ => ((𝓕 w : L2Space E) ξ)) 2 volume := Lp.memLp _
  have key : ∀ n : ℕ, ∀ᵐ ξ ∂volume, (Metric.closedBall (0 : E) n).indicator
      (fun ξ => ((𝓕 w : L2Space E) ξ) - (multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) ξ = 0 := by
    intro n
    set A : Set E := Metric.closedBall (0 : E) n with hA
    have hAmeas : MeasurableSet A := measurableSet_closedBall
    set u : E → ℂ := A.indicator
      (fun ξ => ((𝓕 w : L2Space E) ξ) - (multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) with hudef
    have husupp : ∀ ξ ∉ A, u ξ = 0 := fun ξ hξ => Set.indicator_of_notMem hξ _
    have hu : MemLp u 2 volume := by
      have h1 : MemLp (A.indicator fun ξ => ((𝓕 w : L2Space E) ξ)) 2 volume :=
        hWm.indicator hAmeas
      have h2 : MemLp (A.indicator fun ξ => (multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) 2 volume := by
        have h3 : MemLp (A.indicator fun ξ => ((𝓕 z : L2Space E) ξ)) 2 volume :=
          hZm.indicator hAmeas
        have h4 := memLp_multiplier_mul_of_support n h3
          (fun ξ hξ => Set.indicator_of_notMem hξ _)
        refine MemLp.ae_eq ?_ h4
        filter_upwards with ξ
        by_cases hξ : ξ ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hξ]
      have h5 : u = (A.indicator fun ξ => ((𝓕 w : L2Space E) ξ))
          - A.indicator (fun ξ => (multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) := by
        funext ξ
        by_cases hξ : ξ ∈ A <;>
          simp [hudef, Set.indicator_of_mem, Set.indicator_of_notMem, hξ]
      rw [h5]
      exact h1.sub h2
    have hmu : MemLp (fun ξ => (multiplier ξ : ℂ) * u ξ) 2 volume :=
      memLp_multiplier_mul_of_support n hu husupp
    obtain ⟨Y, hY1, hY2⟩ := exists_mem_adjoint_domain hu hmu
    have hpair := h Y
    have hLHS : inner ℂ w (Y : L2Space E)
        = ∫ ξ, (starRingEnd ℂ) ((𝓕 w : L2Space E) ξ) * u ξ := by
      rw [inner_eq_integral_fourier]
      refine integral_congr_ae ?_
      filter_upwards [hY1] with ξ hξ
      rw [hξ]
    have hRHS : inner ℂ z ((freeLaplacian (E := E)).adjoint Y)
        = ∫ ξ, (starRingEnd ℂ) ((multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) * u ξ := by
      rw [inner_eq_integral_fourier]
      refine integral_congr_ae ?_
      filter_upwards [hY2] with ξ hξ
      rw [hξ, map_mul, Complex.conj_ofReal]
      ring
    have hint1 : Integrable
        (fun ξ => (starRingEnd ℂ) ((𝓕 w : L2Space E) ξ) * u ξ) volume := by
      simpa [Pi.mul_def] using (memLp_conj hWm).integrable_mul hu
    have hint2 : Integrable
        (fun ξ => (starRingEnd ℂ) ((multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) * u ξ) volume := by
      have h0 : Integrable
          (fun ξ => (starRingEnd ℂ) ((𝓕 z : L2Space E) ξ) * ((multiplier ξ : ℂ) * u ξ)) volume := by
        simpa [Pi.mul_def] using (memLp_conj hZm).integrable_mul hmu
      refine h0.congr ?_
      filter_upwards with ξ
      rw [map_mul, Complex.conj_ofReal]
      ring
    have hzero : ∫ ξ, (starRingEnd ℂ) (u ξ) * u ξ = 0 := by
      have hsplit : ∫ ξ, (starRingEnd ℂ) (u ξ) * u ξ
          = (∫ ξ, (starRingEnd ℂ) ((𝓕 w : L2Space E) ξ) * u ξ)
            - ∫ ξ, (starRingEnd ℂ) ((multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) * u ξ := by
        rw [← integral_sub hint1 hint2]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        dsimp only
        by_cases hξ : ξ ∈ A
        · have hval : u ξ = ((𝓕 w : L2Space E) ξ) - (multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ) :=
            Set.indicator_of_mem hξ _
          rw [hval, map_sub]
          ring
        · rw [husupp ξ hξ]
          ring
      rw [hsplit, ← hLHS, ← hRHS, hpair, sub_self]
    have hUzero : hu.toLp u = 0 := by
      refine inner_self_eq_zero (𝕜 := ℂ).mp ?_
      rw [MeasureTheory.L2.inner_def]
      rw [← hzero]
      refine integral_congr_ae ?_
      filter_upwards [hu.coeFn_toLp] with ξ hξ
      rw [hξ, RCLike.inner_apply]
      ring
    have : u =ᵐ[volume] 0 := by
      have h1 := hu.coeFn_toLp
      rw [hUzero] at h1
      filter_upwards [h1, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure E))] with ξ h2 h3
      rw [← h2, h3]
    filter_upwards [this] with ξ hξ using hξ
  have hall : ∀ᵐ ξ ∂volume, ∀ n : ℕ, (Metric.closedBall (0 : E) n).indicator
      (fun ξ => ((𝓕 w : L2Space E) ξ) - (multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) ξ = 0 :=
    ae_all_iff.2 key
  filter_upwards [hall] with ξ hξ
  obtain ⟨n, hn⟩ := exists_nat_ge ‖ξ‖
  have h1 := hξ n
  rw [Set.indicator_of_mem (by simpa [Metric.mem_closedBall, dist_zero_right] using hn)] at h1
  exact (sub_eq_zero.mp h1).symm

