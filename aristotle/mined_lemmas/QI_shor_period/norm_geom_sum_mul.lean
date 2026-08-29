/-
The quantum period-finding subroutine: the state produced by the algorithm,
the measurement distribution of the first register, and the lower bound on the
probability of a "good" measurement outcome.
-/
import Mathlib
import RequestProject.Analysis

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 2000000

namespace QI

/-- The primitive `Q`-th root of unity `e^{2πi/Q}` used by the quantum Fourier transform. -/

theorem norm_geom_sum_mul (A : ℕ) (x : ℝ) :
    ‖∑ l ∈ Finset.range A, Complex.exp ((x : ℂ) * Complex.I) ^ l‖ * |Real.sin (x / 2)| =
      |Real.sin (A * x / 2)| := by
  set z := Complex.exp ((x : ℂ) * Complex.I) with hz
  by_cases h : z = 1
  · have hs : Real.sin (x / 2) = 0 := (exp_eq_one_iff_sin_half x).mp h
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
    have hxk : x = 2 * k * Real.pi := by linarith
    rw [hs, abs_zero, mul_zero, hxk,
      show (A : ℝ) * (2 * k * Real.pi) / 2 = ((A * k : ℤ) : ℝ) * Real.pi by push_cast; ring,
      Real.sin_int_mul_pi, abs_zero]
  · rw [geom_sum_eq h, norm_div]
    have hzA : z ^ A = Complex.exp ((((A : ℝ) * x : ℝ) : ℂ) * Complex.I) := by
      rw [hz, ← Complex.exp_nat_mul]; push_cast; ring_nf
    rw [hzA, norm_exp_sub_one, hz, norm_exp_sub_one]
    have hne : |Real.sin (x / 2)| ≠ 0 := by
      simp only [ne_eq, abs_eq_zero]
      exact fun h0 => h ((exp_eq_one_iff_sin_half x).mpr h0)
    field_simp

