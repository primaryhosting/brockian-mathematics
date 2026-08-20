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

lemma norm_avg_le (x : ℕ → AddCircle T) (f : C(AddCircle T, ℂ)) (N : ℕ) :
    ‖avg x f N‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [avg, norm_nonneg f]
  · rw [avg, norm_mul, norm_inv]
    have h1 : ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ N * ‖f‖ := by
      calc ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ ∑ n ∈ Finset.range N, ‖f (x n)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ := Finset.sum_le_sum (fun n _ => f.norm_coe_le_norm _)
        _ = N * ‖f‖ := by simp
    have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [Complex.norm_natCast, inv_mul_le_iff₀ hNpos]
    simpa [mul_comm] using h1

