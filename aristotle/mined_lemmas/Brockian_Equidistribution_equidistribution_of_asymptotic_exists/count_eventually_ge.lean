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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

open Filter Topology MeasureTheory Complex

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian.Equidistribution

/-! ## Weyl averages of continuous functions on the circle -/

/-- The `N`-th Weyl average of a continuous function `f` on the circle `ℝ / ℤ`, sampled along the
orbit `n ↦ n • α` of the rotation by `α`. -/

theorem count_eventually_ge {α : ℝ} (hα : Irrational α) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (b - a) - ε ≤ (countIco α a b N : ℝ) / N := by
  rcases le_or_gt (b - a) ε with hcase | hcase
  · filter_upwards with N
    have h : (0 : ℝ) ≤ (countIco α a b N : ℝ) / N := by positivity
    linarith
  set δ : ℝ := min (ε / 4) ((b - a) / 4) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ ε / 4 := min_le_left _ _
  have hδ2 : δ ≤ (b - a) / 4 := min_le_right _ _
  have hmid : a + δ ≤ b - δ := by linarith
  set g : C(AddCircle (1 : ℝ), ℝ) := trapCM a b δ hδ ha hb with hg
  have hI : (b - a) - 2 * δ ≤ ∫ x, g x := by
    rw [hg, trapCM_integral]
    exact trap_integral_ge a b δ hδ ha hb hmid
  have htend := tendsto_weylAvg_real hα g
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N₀, hN₀⟩ := htend δ hδ
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hd := hN₀ N hN
  rw [Real.dist_eq, abs_lt] at hd
  have havg : (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, g (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ))
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, trap a b δ (Int.fract ((n : ℝ) * α)) := by
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [coe_eq_coe_fract, hg,
      trapCM_apply a b δ hδ ha hb _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩]
  have hle : (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, trap a b δ (Int.fract ((n : ℝ) * α))
      ≤ (countIco α a b N : ℝ) / N := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (sum_trap_le_count α a b δ hδ N) (by positivity)
  rw [havg] at hd
  linarith [hd.1, hle]

/-! ## The main theorem -/

/-- **Weyl's equidistribution theorem.** For every irrational `α` and every subinterval
`[a, b) ⊆ [0, 1]`, the proportion of the first `N` points of the sequence of fractional parts
`(fract (n α))ₙ` that lie in `[a, b)` converges to the length `b - a` of the interval.

In particular the asymptotic frequency exists (and is unconditional: no hypothesis beyond the
irrationality of `α` is assumed). -/
