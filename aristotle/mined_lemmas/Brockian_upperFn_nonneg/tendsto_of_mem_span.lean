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

import Brockian.WeylEquidistribution

/-!
# Equidistribution: reduction of a configuration count to its main term

Fix an irrational number `a`, a point `c` on the circle `ℝ/ℤ` and a radius `r` with
`0 < r < 1/2`.  Call `n` *admissible* if the orbit point `n • a` lies within distance `r` of `c`
on `ℝ/ℤ`.  `configCount a c r N` counts the admissible `n < N`, and the expected main term is
`mainTerm r N = 2 * r * N` (the measure of the arc times the number of trials).

The main result `configCount_over_main_tendsto` states that the ratio of the count to the main
term tends to `1`.

The analytic input is Weyl's equidistribution theorem for continuous test functions, proved in
`Brockian.WeylEquidistribution`; the passage from continuous test functions to the (bounded
variation, indeed indicator) test function of an arc is done here by sandwiching the indicator
between two explicit continuous, piecewise-linear functions.
-/

open MeasureTheory Filter Topology Metric
open scoped BigOperators

namespace Brockian
namespace EquidistributionBVReduction

open Brockian.Weyl

noncomputable section

open scoped Classical in
/-- The number of `n < N` for which the orbit point `n • a` lies within distance `r` of `c`
on the circle `ℝ/ℤ`. -/

lemma tendsto_of_mem_span (a : ℝ) (ha : Irrational a) (f : C(Circ, ℂ))
    (hf : f ∈ span ℂ (Set.range (fourier : ℤ → C(Circ, ℂ)))) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (pt a n))
      atTop (𝓝 (∫ x : Circ, f x)) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      rcases eq_or_ne m 0 with rfl | hm
      · rw [integral_fourier 0, if_pos rfl]
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        simp only [fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        field_simp
      · rw [integral_fourier m, if_neg hm]
        exact weyl_sum_tendsto a ha hm
  | zero => simp
  | add x y hx hy ihx ihy =>
      simp only [ContinuousMap.add_apply, Finset.sum_add_distrib, mul_add]
      rw [integral_add (integrable_continuous x) (integrable_continuous y)]
      exact ihx.add ihy
  | smul c x hx ihx =>
      simp only [ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      rw [integral_const_mul]
      exact (ihx.const_mul c).congr (fun N => by ring)

/-- **Weyl's equidistribution theorem** for continuous complex-valued test functions. -/
