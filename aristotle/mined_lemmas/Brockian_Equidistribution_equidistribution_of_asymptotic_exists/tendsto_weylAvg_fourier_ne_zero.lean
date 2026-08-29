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

theorem tendsto_weylAvg_fourier_ne_zero (α : ℝ) {k : ℤ}
    (hz : Complex.exp (2 * (Real.pi : ℂ) * I * k * α) ≠ 1) :
    Tendsto (weylAvg α (fourier k)) atTop (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * (Real.pi : ℂ) * I * k * α) with hzdef
  have habs : ‖z‖ = 1 := by rw [hzdef, Complex.norm_exp]; simp
  have hsum : ∀ N : ℕ, ∑ n ∈ Finset.range N,
      fourier k (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ)) = (z ^ N - 1) / (z - 1) := by
    intro N
    rw [← geom_sum_eq hz]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [fourier_coe_apply, hzdef, ← Complex.exp_nat_mul]
    push_cast; ring_nf
  have hden : (0 : ℝ) < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hbound : ∀ N : ℕ, ‖weylAvg α (fourier k) N‖ ≤ (2 / ‖z - 1‖) / N := by
    intro N
    have h2 : ‖z ^ N - 1‖ ≤ 2 :=
      calc ‖z ^ N - 1‖ ≤ ‖(z : ℂ) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, habs]; norm_num
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp [weylAvg]
    · have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      rw [weylAvg, hsum N, norm_mul, norm_div, norm_inv, Complex.norm_natCast]
      calc (N : ℝ)⁻¹ * (‖z ^ N - 1‖ / ‖z - 1‖) = ‖z ^ N - 1‖ / (‖z - 1‖ * N) := by ring
        _ ≤ 2 / (‖z - 1‖ * N) := by gcongr
        _ = (2 / ‖z - 1‖) / N := by ring
  exact squeeze_zero_norm hbound (tendsto_const_div_atTop_nhds_zero_nat _)

