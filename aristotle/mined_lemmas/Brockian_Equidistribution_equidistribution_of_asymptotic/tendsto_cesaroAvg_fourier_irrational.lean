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

open MeasureTheory Filter Topology AddCircle

namespace Brockian.Equidistribution

/-- The Cesàro (Birkhoff) average of `f` along the first `N` terms of the sequence `x`. -/

theorem tendsto_cesaroAvg_fourier_irrational {a : ℝ} (ha : Irrational a) {k : ℤ} (hk : k ≠ 0) :
    Tendsto (cesaroAvg (fun n : ℕ => ((n * a : ℝ) : AddCircle (1 : ℝ))) (fourier k)) atTop
      (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * k * a) with hzdef
  have hz1 : z ≠ 1 := by
    intro h
    rw [hzdef, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (k : ℂ) * (a : ℂ) = (m : ℂ) := by
      have h4 : (2 * (Real.pi : ℂ) * Complex.I) * ((k : ℂ) * a)
          = (2 * (Real.pi : ℂ) * Complex.I) * m := by linear_combination hm
      exact mul_left_cancel₀ (by simp [hpi, Complex.I_ne_zero]) h4
    exact (ha.intCast_mul hk).ne_int m (by exact_mod_cast h2)
  have hznorm : ‖z‖ = 1 := by rw [hzdef, Complex.norm_exp]; norm_num
  have hterm : ∀ n : ℕ, fourier (T := 1) k ((n * a : ℝ) : AddCircle (1 : ℝ)) = z ^ n := by
    intro n
    rw [fourier_coe_apply, hzdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz0 : (0 : ℝ) < ‖z - 1‖ := by simpa [sub_eq_zero] using hz1
  have hbound : ∀ N : ℕ, ‖cesaroAvg (fun n : ℕ => ((n * a : ℝ) : AddCircle (1 : ℝ))) (fourier k) N‖
      ≤ (N : ℝ)⁻¹ * (2 / ‖z - 1‖) := by
    intro N
    have hEq : cesaroAvg (fun n : ℕ => ((n * a : ℝ) : AddCircle (1 : ℝ))) (fourier k) N
        = (N : ℂ)⁻¹ * ((z ^ N - 1) / (z - 1)) := by
      rw [cesaroAvg]
      simp only [hterm]
      rw [geom_sum_eq hz1]
    rw [hEq, norm_mul, norm_inv, Complex.norm_natCast, norm_div]
    have h1 : ‖z ^ N - 1‖ ≤ 2 := by
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hznorm]; norm_num
    gcongr
  refine squeeze_zero_norm' (Eventually.of_forall hbound) ?_
  simpa using (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.mul_const (2 / ‖z - 1‖)

/-- **Weyl's equidistribution theorem for irrational rotations.**  For irrational `a`, the
sequence `n ↦ n * a` is equidistributed in `ℝ/ℤ`: the Cesàro averages of every continuous
function converge to its integral against the Haar probability measure. -/
