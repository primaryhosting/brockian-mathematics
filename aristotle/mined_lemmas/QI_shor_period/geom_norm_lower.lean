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

theorem geom_norm_lower (A : ℕ) (t : ℝ) (h : |(A : ℝ) * t| ≤ 5 / 8) :
    (6 / (5 * Real.pi)) * A ≤
      ‖∑ l ∈ Finset.range A, Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) ^ l‖ := by
  have hpi := Real.pi_gt_three
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_pow,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Complex.norm_natCast]
    have : (6 : ℝ) / (5 * Real.pi) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) A]
  · have hid := norm_geom_sum_mul A (2 * Real.pi * t)
    rw [show (2 * Real.pi * t) / 2 = Real.pi * t by ring] at hid
    rw [show (A : ℝ) * (2 * Real.pi * t) / 2 = Real.pi * ((A : ℝ) * t) by ring] at hid
    have hlow := sin_pi_lower ((A : ℝ) * t) h
    have hup : |Real.sin (Real.pi * t)| ≤ Real.pi * |t| := by
      have := Real.abs_sin_le_abs (x := Real.pi * t)
      rwa [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.pi)] at this
    have hnn : 0 ≤ ‖∑ l ∈ Finset.range A,
        Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) ^ l‖ := norm_nonneg _
    set S := ‖∑ l ∈ Finset.range A,
      Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) ^ l‖
    have habs : |(A : ℝ) * t| = (A : ℝ) * |t| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg A)]
    have ht0 : 0 < |t| := abs_pos.mpr ht
    have h1 : (6 / 5) * ((A : ℝ) * |t|) ≤ S * (Real.pi * |t|) := by
      calc (6 / 5) * ((A : ℝ) * |t|) = (6 / 5) * |(A : ℝ) * t| := by rw [habs]
        _ ≤ |Real.sin (Real.pi * ((A : ℝ) * t))| := hlow
        _ = S * |Real.sin (Real.pi * t)| := hid.symm
        _ ≤ S * (Real.pi * |t|) := by nlinarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith

end QI

/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Analysis
import RequestProject.Quantum

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

set_option grind.warning false

namespace QI

/-! ### Classical post-processing -/

/-- The classical post-processing of Shor's algorithm succeeds on the measurement
outcome `m`: some reduced fraction `p/q` with denominator `q ≤ N` lies within
`1/(2Q)` of `m/Q` (so the continued-fraction expansion of `m/Q` returns an answer),
and every such fraction has denominator exactly the period `r`. -/
