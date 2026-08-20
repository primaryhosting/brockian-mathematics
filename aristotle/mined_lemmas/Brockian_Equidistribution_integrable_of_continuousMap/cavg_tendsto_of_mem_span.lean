import Brockian.Equidistribution

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
# Weyl equidistribution

This file develops, from scratch, Weyl's criterion for equidistribution modulo one and applies
it to the sequence `n ↦ n * α` for irrational `α`.

The main statement is `Brockian.Equidistribution.equidistribution_of_asymptotic_exists`, which
is *conditional* on the asymptotic vanishing of the Weyl exponential sums, and its unconditional
consequence `Brockian.Equidistribution.equidistributedMod1_natMul_irrational`.
-/

namespace Brockian.Equidistribution

open MeasureTheory Filter Finset Complex Topology Metric

open scoped Real

noncomputable section

/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

theorem cavg_tendsto_of_mem_span (x : ℕ → ℝ) (hx : WeylCondition x)
    {f : C(AddCircle (1 : ℝ), ℂ)} (hf : f ∈ Submodule.span ℂ (Set.range (@fourier 1))) :
    Tendsto (cavg x f) atTop (𝓝 (∫ z, f z)) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨h, rfl⟩ := hg
      rcases eq_or_ne h 0 with rfl | hh
      · have hint : (∫ z : AddCircle (1 : ℝ), (fourier (0 : ℤ)) z) = 1 := by simp
        rw [hint]
        refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℂ)))
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        simp [cavg, inv_mul_cancel₀ hN0]
      · rw [integral_fourier_eq_zero hh]
        exact hx h hh
  | zero =>
      refine Tendsto.congr (f₁ := fun _ => (0 : ℂ)) (fun N => by simp [cavg]) ?_
      simp only [ContinuousMap.zero_apply, integral_zero]
      exact tendsto_const_nhds
  | add g1 g2 _ _ ih1 ih2 =>
      refine Tendsto.congr (f₁ := fun N => cavg x g1 N + cavg x g2 N)
        (fun N => by simp [cavg, Finset.sum_add_distrib, mul_add]) ?_
      simp only [ContinuousMap.add_apply]
      rw [integral_add (integrable_of_continuousMap g1) (integrable_of_continuousMap g2)]
      exact ih1.add ih2
  | smul c g _ ih =>
      refine Tendsto.congr (f₁ := fun N => c * cavg x g N)
        (fun N => by simp [cavg, Finset.mul_sum, mul_left_comm]) ?_
      simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
      exact ih.const_mul c

/-! ### Weyl's criterion, step 2: all continuous functions -/

