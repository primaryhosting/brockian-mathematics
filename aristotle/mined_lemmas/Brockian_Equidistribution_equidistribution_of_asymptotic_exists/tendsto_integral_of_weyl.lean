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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: this Lean toolchain requires `import` to be the very first command in a file, so the
required header comment appears immediately after the import.)
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Real BigOperators

namespace Brockian.Equidistribution

/-- The circle `ℝ / ℤ`, on which we study equidistribution. -/
abbrev Circ : Type := AddCircle (1 : ℝ)

noncomputable instance : IsProbabilityMeasure (volume : Measure Circ) := ⟨by simp⟩

/-- Continuous functions on the (compact) circle are integrable for any finite measure. -/

lemma tendsto_integral_of_weyl (x : ℕ → Circ)
    (hW : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ => ∫ t, (fourier h : C(Circ, ℂ)) t ∂(emp x N)) atTop (𝓝 0))
    (f : C(Circ, ℂ)) :
    Tendsto (fun N : ℕ => ∫ t, f t ∂(emp x N)) atTop
      (𝓝 (∫ t, f t ∂(volume : Measure Circ))) := by
  -- the span of the Fourier monomials consists of good functions
  have hspan : (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) ≤ goodFuns x := by
    rw [Submodule.span_le]
    rintro - ⟨n, rfl⟩
    rw [SetLike.mem_coe, mem_goodFuns, GoodFun]
    rcases eq_or_ne n 0 with rfl | hn
    · have h0 : ∀ μ : Measure Circ, IsProbabilityMeasure μ →
          ∫ t, (fourier (0 : ℤ) : C(Circ, ℂ)) t ∂μ = 1 := by
        intro μ hμ
        simp
      simp only [h0 _ (instIsProbEmp x _), h0 _ inferInstance]
      exact tendsto_const_nhds
    · rw [integral_fourier_eq_zero hn]
      exact hW n hn
  -- and the span is dense
  have hfmem : f ∈ closure ((Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) : Set _) := by
    have : (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure = ⊤ :=
      span_fourier_closure_eq_top
    have hmem : f ∈ (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure := by
      rw [this]; trivial
    exact hmem
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgmem, hg⟩ := Metric.mem_closure_iff.mp hfmem (ε / 3) (by positivity)
  have hgood : GoodFun x g := hspan hgmem
  rw [GoodFun, Metric.tendsto_atTop] at hgood
  obtain ⟨N₀, hN₀⟩ := hgood (ε / 3) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have hfg : ‖f - g‖ < ε / 3 := by
    rw [dist_eq_norm] at hg
    exact hg
  have h1 : ‖(∫ t, f t ∂(emp x N)) - ∫ t, g t ∂(emp x N)‖ ≤ ‖f - g‖ :=
    norm_integral_sub_le _ f g
  have h2 : ‖(∫ t, g t ∂(volume : Measure Circ)) - ∫ t, f t ∂(volume : Measure Circ)‖ ≤ ‖f - g‖ := by
    have := norm_integral_sub_le (volume : Measure Circ) g f
    rwa [show ‖g - f‖ = ‖f - g‖ from norm_sub_rev g f] at this
  have h3 : dist (∫ t, g t ∂(emp x N)) (∫ t, g t ∂(volume : Measure Circ)) < ε / 3 := hN₀ N hN
  rw [dist_eq_norm] at h3 ⊢
  calc ‖(∫ t, f t ∂(emp x N)) - ∫ t, f t ∂(volume : Measure Circ)‖
      = ‖((∫ t, f t ∂(emp x N)) - ∫ t, g t ∂(emp x N)) +
          (((∫ t, g t ∂(emp x N)) - ∫ t, g t ∂(volume : Measure Circ)) +
            ((∫ t, g t ∂(volume : Measure Circ)) - ∫ t, f t ∂(volume : Measure Circ)))‖ := by
        ring_nf
    _ ≤ ‖(∫ t, f t ∂(emp x N)) - ∫ t, g t ∂(emp x N)‖ +
          (‖(∫ t, g t ∂(emp x N)) - ∫ t, g t ∂(volume : Measure Circ)‖ +
            ‖(∫ t, g t ∂(volume : Measure Circ)) - ∫ t, f t ∂(volume : Measure Circ)‖) :=
        le_trans (norm_add_le _ _) (by gcongr; exact norm_add_le _ _)
    _ < ε := by linarith

/-- Weak convergence of the empirical measures to the Haar (Lebesgue) probability measure. -/
