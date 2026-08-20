import Brockian.EquidistributionBVReduction

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
# Equidistribution of `n • α` and the reduction of configuration counts to the main term

For an irrational `α`, the configuration count

`configCount α a b N = #{ n < N : Int.fract (n * α) ∈ [a, b) }`

is asymptotic to its main term `mainTerm a b N = (b - a) * N`.

The analytic input (Weyl equidistribution of the sequence `n • α` on the circle `ℝ / ℤ`)
is proved here from scratch, so the final statement
`configCount_over_main_tendsto` is unconditional.

The proof proceeds by:
* computing the Birkhoff averages of the Fourier monomials `fourier k` along the orbit
  (geometric sums, `avg_fourier_tendsto`);
* extending to all continuous functions by Stone--Weierstrass (`avg_continuous_tendsto`);
* sandwiching the indicator of an arc between continuous piecewise-linear functions
  (a bounded-variation reduction) to obtain the counting asymptotics.
-/

open Filter MeasureTheory Set Topology Complex
open scoped BigOperators

set_option autoImplicit false

namespace Brockian

namespace EquidistributionBVReduction

noncomputable section

local instance isProbabilityMeasure_volume_unitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- The point `n * α` of the circle `ℝ / ℤ`. -/

theorem avg_sub_le (alpha : ℝ) (f g : C(UnitAddCircle, ℂ)) (N : ℕ) :
    ‖avg alpha f N - avg alpha g N‖ ≤ ‖f - g‖ := by
  have hsum : ‖∑ n ∈ Finset.range N, (f (orbit alpha n) - g (orbit alpha n))‖ ≤ N * ‖f - g‖ := by
    calc ‖∑ n ∈ Finset.range N, (f (orbit alpha n) - g (orbit alpha n))‖
        ≤ ∑ n ∈ Finset.range N, ‖f (orbit alpha n) - g (orbit alpha n)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, ‖f - g‖ := by
          refine Finset.sum_le_sum fun n _ => ?_
          simpa using (f - g).norm_coe_le_norm (orbit alpha n)
      _ = N * ‖f - g‖ := by simp
  have hrw : avg alpha f N - avg alpha g N
      = (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, (f (orbit alpha n) - g (orbit alpha n)) := by
    simp [avg, Finset.sum_sub_distrib, smul_sub]
  rw [hrw, norm_smul, norm_inv, Real.norm_natCast]
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · rw [inv_mul_le_iff₀ (by exact_mod_cast h)]
    exact hsum

