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
# Weyl's equidistribution criterion on the additive circle

This file develops equidistribution of sequences on `AddCircle T`.

* `Brockian.Equidistribution.Equidistributed x` says that the empirical averages of a sequence
  `x : ℕ → AddCircle T` converge, against every continuous test function, to the integral of the
  test function with respect to the normalised Haar (probability) measure.
* `Brockian.Equidistribution.WeylSumsVanish x` is the Weyl-sum hypothesis: the empirical averages
  of every nontrivial Fourier monomial `fourier k` (`k ≠ 0`) tend to `0`.
* `Brockian.Equidistribution.equidistribution_of_asymptotic` is the conditional statement
  (Weyl's criterion): `WeylSumsVanish x → Equidistributed x`.
* `Brockian.Equidistribution.weylSumsVanish_rotSeq` discharges the hypothesis for the
  irrational rotation sequence `n ↦ n * a` on `AddCircle 1`, and
  `Brockian.Equidistribution.equidistributed_irrational_rotation` is the resulting unconditional
  equidistribution theorem.
-/

open Filter Topology MeasureTheory AddCircle Complex Submodule Set

namespace Brockian.Equidistribution

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The empirical average of `f` over the first `N` terms of the sequence `x`. -/

theorem equidistribution_of_asymptotic (x : ℕ → AddCircle T) (hx : WeylSumsVanish x) :
    Equidistributed x := by
  intro f
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgspan, hg⟩ := exists_mem_span_norm_sub_lt f (ε := ε / 3) (by positivity)
  have hgt := tendsto_avg_of_mem_span x hx g hgspan
  rw [Metric.tendsto_atTop] at hgt
  obtain ⟨N₀, hN₀⟩ := hgt (ε / 3) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : ‖avg x ⇑f N - avg x ⇑g N‖ ≤ ε / 3 := by
    have he : avg x ⇑f N - avg x ⇑g N = avg x (⇑(f - g)) N := by
      simpa using (avg_sub x ⇑f ⇑g N).symm
    rw [he]
    exact (norm_avg_le x (f - g) N).trans hg.le
  have h2 : ‖avg x ⇑g N - ∫ t, g t ∂haarAddCircle‖ < ε / 3 := by
    have := hN₀ N hN
    rwa [dist_eq_norm] at this
  have h3 : ‖(∫ t, g t ∂haarAddCircle) - ∫ t, f t ∂haarAddCircle‖ ≤ ε / 3 := by
    have he : (∫ t, g t ∂haarAddCircle) - ∫ t, f t ∂haarAddCircle
        = ∫ t, (g - f) t ∂haarAddCircle := by
      simpa using
        (integral_sub (integrable_of_continuousMap g) (integrable_of_continuousMap f)).symm
    rw [he]
    refine (norm_integral_le (g - f)).trans ?_
    rw [← norm_neg, neg_sub]
    exact hg.le
  have hsplit : dist (avg x ⇑f N) (∫ t, f t ∂haarAddCircle)
      ≤ ‖avg x ⇑f N - avg x ⇑g N‖ + ‖avg x ⇑g N - ∫ t, g t ∂haarAddCircle‖
        + ‖(∫ t, g t ∂haarAddCircle) - ∫ t, f t ∂haarAddCircle‖ := by
    rw [dist_eq_norm]
    have : avg x ⇑f N - ∫ t, f t ∂haarAddCircle
        = (avg x ⇑f N - avg x ⇑g N) + (avg x ⇑g N - ∫ t, g t ∂haarAddCircle)
          + ((∫ t, g t ∂haarAddCircle) - ∫ t, f t ∂haarAddCircle) := by ring
    rw [this]
    exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
  linarith

section Rotation

/-- The rotation sequence `n ↦ n * a` on `AddCircle 1`. -/
