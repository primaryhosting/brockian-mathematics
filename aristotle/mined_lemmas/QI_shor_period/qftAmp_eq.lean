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

theorem qftAmp_eq (Q : ℕ) (f : ℕ → β) (m : ℕ) (y : β) :
    qftAmp Q f m y =
      (Q : ℂ)⁻¹ * ∑ j ∈ (Finset.range Q).filter (fun j => f j = y), omega Q ^ (j * m) := by
  rw [qftAmp, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  have h : oracleAmp Q f j y = if f j = y then ((Real.sqrt Q : ℝ) : ℂ)⁻¹ else 0 := by
    rw [oracleAmp]; simp [hj]
  rw [h]
  by_cases hy : f j = y
  · simp only [hy, if_pos, ← inv_sqrt_sq Q]
    ring
  · simp [hy]

section Periodic

variable (f : ℕ → β) (Q r : ℕ)

/-- For a function with exact period `r`, the fibre of `f k` inside `[0, Q)` is an
arithmetic progression of step `r`. -/
