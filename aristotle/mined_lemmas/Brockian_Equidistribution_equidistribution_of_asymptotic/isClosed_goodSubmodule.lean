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
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The block above is repeated as the file header; Lean does not allow a module docstring to
precede the `import` line.)

This file proves **Weyl's equidistribution criterion** unconditionally: if all nontrivial
exponential sums of a real sequence `x` are asymptotically negligible, then `x` is
equidistributed modulo one.  The argument goes through the circle `𝕋 = AddCircle 1`:

* the Birkhoff averages of each Fourier monomial converge to its integral (`avgC_fourier_tendsto`);
* the set of continuous functions with this property is a closed submodule of `C(𝕋, ℂ)`, hence,
  by Stone-Weierstrass (`span_fourier_closure_eq_top`), is everything (`avgC_tendsto`);
* indicator functions of arcs are squeezed between continuous plateau functions supported on
  metric balls, whose integrals are controlled by `AddCircle.volume_closedBall`.

As an application (and as a witness that the hypothesis is satisfiable) we derive the classical
equidistribution of irrational rotations, `equidistribution_irrational_rotation`.
-/

open Filter MeasureTheory Metric Complex Set
open scoped Topology Real BigOperators

namespace Brockian.Equidistribution

local notation "𝕋" => AddCircle (1 : ℝ)

/-- The Birkhoff/Weyl average of a complex-valued continuous function on the circle along the
first `N` terms of the sequence `x`. -/

lemma isClosed_goodSubmodule (x : ℕ → ℝ) :
    IsClosed ((goodSubmodule x : Submodule ℂ C(𝕋, ℂ)) : Set C(𝕋, ℂ)) := by
  rw [← closure_subset_iff_isClosed]
  intro F hF
  show Tendsto (avgC x F) atTop (𝓝 (∫ z : 𝕋, F z ∂AddCircle.haarAddCircle))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨G, hGmem, hGdist⟩ := Metric.mem_closure_iff.1 hF (ε / 3) (by linarith)
  have hGgood : Tendsto (avgC x G) atTop (𝓝 (∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)) := hGmem
  rw [Metric.tendsto_atTop] at hGgood
  obtain ⟨N₀, hN₀⟩ := hGgood (ε / 3) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : ‖avgC x F N - avgC x G N‖ ≤ ‖F - G‖ := by
    rw [avgC_sub]; exact norm_avgC_le x (F - G) N
  have h2 : ‖(∫ z : 𝕋, F z ∂AddCircle.haarAddCircle)
      - ∫ z : 𝕋, G z ∂AddCircle.haarAddCircle‖ ≤ ‖F - G‖ := by
    have : (∫ z : 𝕋, F z ∂AddCircle.haarAddCircle)
        - (∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)
        = ∫ z : 𝕋, (F - G) z ∂AddCircle.haarAddCircle := by
      simp only [ContinuousMap.sub_apply]
      exact (integral_sub (contMapC_integrable F) (contMapC_integrable G)).symm
    rw [this]
    exact norm_integral_le_norm (F - G)
  have hFG : ‖F - G‖ < ε / 3 := by
    rw [← dist_eq_norm]; exact hGdist
  have h3 := hN₀ N hN
  rw [dist_eq_norm] at h3 ⊢
  calc ‖avgC x F N - ∫ z : 𝕋, F z ∂AddCircle.haarAddCircle‖
      = ‖(avgC x F N - avgC x G N) + (avgC x G N - ∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)
          + ((∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)
              - ∫ z : 𝕋, F z ∂AddCircle.haarAddCircle)‖ := by ring_nf
    _ ≤ ‖(avgC x F N - avgC x G N) + (avgC x G N - ∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)‖
          + ‖(∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)
              - ∫ z : 𝕋, F z ∂AddCircle.haarAddCircle‖ := norm_add_le _ _
    _ ≤ ‖avgC x F N - avgC x G N‖ + ‖avgC x G N - ∫ z : 𝕋, G z ∂AddCircle.haarAddCircle‖
          + ‖(∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)
              - ∫ z : 𝕋, F z ∂AddCircle.haarAddCircle‖ := by
          gcongr; exact norm_add_le _ _
    _ < ε := by
          rw [norm_sub_rev (∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)] at *
          linarith

