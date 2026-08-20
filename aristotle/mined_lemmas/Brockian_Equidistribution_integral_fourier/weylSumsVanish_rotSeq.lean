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

theorem weylSumsVanish_rotSeq {a : ℝ} (ha : Irrational a) : WeylSumsVanish (rotSeq a) := by
  intro k hk
  set z : ℂ := Complex.exp (((2 * Real.pi * k * a : ℝ) : ℂ) * Complex.I) with hzdef
  have hz1 : z ≠ 1 := exp_ne_one_of_irrational ha hk
  have hznorm : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hd : 0 < ‖z - 1‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hz1
  have havg : ∀ N : ℕ, avg (rotSeq a) (fourier k) N = (N : ℂ)⁻¹ * ((z ^ N - 1) / (z - 1)) := by
    intro N
    simp only [avg, fourier_rotSeq a k, ← hzdef]
    rw [geom_sum_eq hz1]
  refine squeeze_zero_norm (a := fun N : ℕ => (2 / ‖z - 1‖) / N) (fun N => ?_) ?_
  · show ‖avg (rotSeq a) (⇑(fourier k)) N‖ ≤ 2 / ‖z - 1‖ / (N : ℝ)
    rw [havg N, norm_mul, norm_inv, Complex.norm_natCast, norm_div, div_eq_inv_mul (2 / ‖z - 1‖)]
    have h2 : ‖z ^ N - 1‖ ≤ 2 := by
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hznorm]; norm_num
    gcongr
  · exact tendsto_const_div_atTop_nhds_zero_nat _

/-- **Unconditional equidistribution** of the irrational rotation sequence. -/
