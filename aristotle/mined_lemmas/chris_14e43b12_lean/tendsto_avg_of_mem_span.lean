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

lemma tendsto_avg_of_mem_span (x : ℕ → AddCircle T) (hx : WeylSumsVanish x)
    (f : C(AddCircle T, ℂ)) (hf : f ∈ span ℂ (range (fourier (T := T)))) :
    Tendsto (avg x f) atTop (𝓝 (∫ t, f t ∂haarAddCircle)) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨k, rfl⟩ := hg
      rcases eq_or_ne k 0 with rfl | hk
      · rw [integral_fourier, if_pos rfl]
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [eventually_gt_atTop 0] with N hN
        have hNe : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
        simp [avg, hNe]
      · rw [integral_fourier, if_neg hk]
        exact hx k hk
  | zero =>
      have h : ∀ N : ℕ, avg x (⇑(0 : C(AddCircle T, ℂ))) N = 0 := by intro N; simp [avg]
      simp only [ContinuousMap.zero_apply, integral_zero]
      exact tendsto_const_nhds.congr (fun N => (h N).symm)
  | add g h hg hh ihg ihh =>
      have hadd : ∀ N, avg x (⇑(g + h)) N = avg x ⇑g N + avg x ⇑h N := by
        intro N; simpa using avg_add x ⇑g ⇑h N
      rw [show (∫ t, (g + h) t ∂haarAddCircle) = (∫ t, g t ∂haarAddCircle) + ∫ t, h t ∂haarAddCircle
        from by
          simpa using integral_add (integrable_of_continuousMap g) (integrable_of_continuousMap h)]
      exact (ihg.add ihh).congr (fun N => (hadd N).symm)
  | smul c g hg ih =>
      have hs : ∀ N, avg x (⇑(c • g)) N = c * avg x ⇑g N := by
        intro N; simpa using avg_smul x c ⇑g N
      rw [show (∫ t, (c • g) t ∂haarAddCircle) = c * ∫ t, g t ∂haarAddCircle from by
        simp [integral_const_mul]]
      exact (ih.const_mul c).congr (fun N => (hs N).symm)

/-- Trigonometric polynomials are dense in the continuous functions on the circle. -/
