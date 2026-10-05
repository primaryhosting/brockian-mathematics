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

theorem abs_div_sub_div_le (Q r s m : ℕ) (hr : 0 < r) (hQ : 0 < Q)
    (h : 2 * |((r * m : ℕ) : ℤ) - (s : ℤ) * Q| ≤ (r : ℤ)) :
    |(m : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * Q) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hR : 2 * |(r : ℝ) * m - (s : ℝ) * Q| ≤ (r : ℝ) := by
    have := (Int.cast_le (R := ℝ)).mpr h
    push_cast [Int.cast_abs] at this
    exact this
  have he : (m : ℝ) / Q - (s : ℝ) / r = ((r : ℝ) * m - (s : ℝ) * Q) / (r * Q) := by
    field_simp
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (r : ℝ) * Q),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [abs_nonneg ((r : ℝ) * m - (s : ℝ) * Q)]

/-- Two reduced fractions with denominators at most `N` that are both within
`1/(2Q)` of `m/Q` (with `Q ≥ 2N²`) must be equal. -/
