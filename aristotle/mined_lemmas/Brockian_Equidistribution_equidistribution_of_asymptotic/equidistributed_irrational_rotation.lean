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
-/

open MeasureTheory Filter Topology Submodule Set
open AddCircle (haarAddCircle)

namespace Brockian.Equidistribution

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The `N`-th Weyl average of `f` along the sequence `x`, i.e.
`(1/N) * ∑_{n < N} f (x n)` (equal to `0` when `N = 0`). -/

theorem equidistributed_irrational_rotation {a : ℝ} (ha : Irrational (a / T)) :
    Equidistributed (fun n : ℕ => ((n * a : ℝ) : AddCircle T)) := by
  apply equidistribution_of_asymptotic
  intro k hk
  set z : ℂ := fourier k ((a : ℝ) : AddCircle T) with hzdef
  have hz1 : z ≠ 1 := fourier_coe_ne_one ha hk
  have hznorm : ‖z‖ = 1 := norm_fourier_eq_one _
  have hz10 : ‖z - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz1)
  have hterm : ∀ n : ℕ, fourier k ((n * a : ℝ) : AddCircle T) = z ^ n := by
    intro n
    have hcoe : ((n * a : ℝ) : AddCircle T) = n • ((a : ℝ) : AddCircle T) := by
      rw [← nsmul_eq_mul]
      exact (QuotientAddGroup.mk_nsmul _ _ _).symm
    rw [hcoe, hzdef, fourier_nsmul]
  have hbound : ∀ N : ℕ,
      ‖weylAvg (fun n : ℕ => ((n * a : ℝ) : AddCircle T)) (fourier k) N‖
        ≤ (N : ℝ)⁻¹ * (2 / ‖z - 1‖) := by
    intro N
    have hsum : weylAvg (fun n : ℕ => ((n * a : ℝ) : AddCircle T)) (fourier k) N
        = (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, z ^ n := by
      rw [weylAvg]
      exact congrArg _ (Finset.sum_congr rfl fun n _ => hterm n)
    rw [hsum, geom_sum_eq hz1, norm_mul, norm_inv, Complex.norm_natCast, norm_div]
    gcongr
    calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hznorm]; norm_num
  refine squeeze_zero_norm hbound ?_
  simpa using tendsto_inv_atTop_nhds_zero_nat.mul_const (2 / ‖z - 1‖)

end Brockian.Equidistribution

