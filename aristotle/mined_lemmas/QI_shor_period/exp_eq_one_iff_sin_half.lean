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

theorem exp_eq_one_iff_sin_half (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) = 1 ↔ Real.sin (x / 2) = 0 := by
  constructor
  · intro h
    have h2 := norm_exp_sub_one x
    rw [h] at h2
    simpa using h2
  · intro h
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
    have hxk : x = 2 * k * Real.pi := by linarith
    rw [hxk, show ((2 * (k : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I
        = (k : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

/-- The Dirichlet-kernel identity, in a division-free form. -/
