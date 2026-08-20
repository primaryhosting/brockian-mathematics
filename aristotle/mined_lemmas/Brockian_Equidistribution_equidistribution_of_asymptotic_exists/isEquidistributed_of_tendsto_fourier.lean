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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution: existence of the asymptotic average

This file develops Weyl's criterion for equidistribution modulo one on the circle
`AddCircle (1 : ℝ) = ℝ / ℤ`, and deduces from it Weyl's equidistribution theorem for the
sequence `n ↦ n * a` with `a` irrational.

Main results:

* `Brockian.Equidistribution.isEquidistributed_of_tendsto_fourier`: Weyl's criterion.
* `Brockian.Equidistribution.isEquidistributed_irrational`: the orbit of an irrational
  rotation is equidistributed mod 1.
* `Brockian.Equidistribution.equidistribution_of_asymptotic_exists`: unconditional statement
  that for irrational `a` the asymptotic average of any continuous function along `n * a`
  exists and equals the integral of the function.
-/

open MeasureTheory Filter Complex
open scoped Topology BigOperators

namespace Brockian.Equidistribution

local instance factZeroLtOne : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The Birkhoff-type average of a continuous function `f` on the circle `ℝ / ℤ` along the
first `N` points of the real sequence `x`, taken modulo `1`. -/

theorem isEquidistributed_of_tendsto_fourier (x : ℕ → ℝ)
    (h : ∀ k : ℤ, k ≠ 0 → Tendsto (avg x (fourier k)) atTop (𝓝 0)) :
    IsEquidistributed x := by
  set S : Submodule ℂ C(AddCircle (1 : ℝ), ℂ) :=
  { carrier := {f | Tendsto (avg x f) atTop
        (𝓝 (∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle))}
    add_mem' := by
      intro f g hf hg
      simp only [Set.mem_setOf_eq, ContinuousMap.add_apply] at *
      have hav : avg x (f + g) = fun N => avg x f N + avg x g N := by
        funext N; simp [avg, Finset.sum_add_distrib, mul_add]
      rw [integral_add (integrable_circle f) (integrable_circle g), hav]
      exact hf.add hg
    zero_mem' := by
      simp only [Set.mem_setOf_eq]
      have hav : avg x 0 = fun _ => (0 : ℂ) := by funext N; simp [avg]
      rw [hav]; simp
    smul_mem' := by
      intro c f hf
      simp only [Set.mem_setOf_eq, ContinuousMap.smul_apply, smul_eq_mul] at *
      have hav : avg x (c • f) = fun N => c * avg x f N := by
        funext N
        simp only [avg, ContinuousMap.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [integral_const_mul, hav]
      exact hf.const_mul c } with hS
  have hmemS : ∀ f : C(AddCircle (1 : ℝ), ℂ), f ∈ S ↔ Tendsto (avg x f) atTop
      (𝓝 (∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle)) := fun f => Iff.rfl
  -- `S` is closed, by a `3ε`-argument using that averages and integrals are contractions
  -- for the uniform norm.
  have hclosed : IsClosed (S : Set C(AddCircle (1 : ℝ), ℂ)) := by
    rw [← closure_subset_iff_isClosed]
    intro f hf
    rw [SetLike.mem_coe, hmemS, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨g, hgS, hfg⟩ := Metric.mem_closure_iff.1 hf (ε / 3) (by linarith)
    rw [SetLike.mem_coe, hmemS, Metric.tendsto_atTop] at hgS
    obtain ⟨N₀, hN₀⟩ := hgS (ε / 3) (by linarith)
    refine ⟨N₀, fun N hN => ?_⟩
    have hnorm : ‖f - g‖ < ε / 3 := by rwa [← dist_eq_norm]
    have h1 : ‖avg x f N - avg x g N‖ < ε / 3 := by
      rw [← avg_sub]; exact lt_of_le_of_lt (norm_avg_le x _ N) hnorm
    have h2 : dist (avg x g N) (∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle) < ε / 3 :=
      hN₀ N hN
    have h3 : ‖(∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle)
        - ∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle‖ < ε / 3 := by
      rw [← integral_sub (integrable_circle g) (integrable_circle f)]
      have hgf : ∀ t : AddCircle (1 : ℝ), g t - f t = (g - f) t := fun t => rfl
      simp only [hgf]
      calc ‖∫ t : AddCircle (1 : ℝ), (g - f) t ∂AddCircle.haarAddCircle‖ ≤ ‖g - f‖ :=
            norm_integral_le _
        _ = ‖f - g‖ := by rw [norm_sub_rev]
        _ < ε / 3 := hnorm
    rw [dist_eq_norm] at h2 ⊢
    calc ‖avg x f N - ∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle‖
        = ‖(avg x f N - avg x g N)
            + (avg x g N - ∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle)
            + ((∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle)
              - ∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle)‖ := by ring_nf
      _ ≤ ‖(avg x f N - avg x g N)
            + (avg x g N - ∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle)‖
            + ‖(∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle)
              - ∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle‖ := norm_add_le _ _
      _ ≤ ‖avg x f N - avg x g N‖
            + ‖avg x g N - ∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle‖
            + ‖(∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle)
              - ∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle‖ := by
            gcongr; exact norm_add_le _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
      _ = ε := by ring
  -- the characters belong to `S`
  have hspan : Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, hmemS, integral_fourier]
    rcases eq_or_ne k 0 with rfl | hk
    · rw [if_pos rfl]
      have hav : ∀ N : ℕ, 1 ≤ N → avg x (fourier (T := (1 : ℝ)) 0) N = 1 := by
        intro N hN
        simp only [avg, fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        rw [inv_mul_cancel₀]
        exact Nat.cast_ne_zero.mpr (by omega)
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop 1] with N hN using (hav N hN).symm
    · simpa [if_neg hk] using h k hk
  -- the characters span a dense subspace, so `S = ⊤`
  intro f
  have hf : f ∈ (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]; trivial
  have hf3 : f ∈ closure (S : Set C(AddCircle (1 : ℝ), ℂ)) :=
    closure_mono (by exact_mod_cast hspan) hf
  rw [hclosed.closure_eq] at hf3
  exact (hmemS f).1 hf3

/-- For irrational `a` and `k ≠ 0`, the complex number `exp (2 π i k a)` is not equal to `1`. -/
