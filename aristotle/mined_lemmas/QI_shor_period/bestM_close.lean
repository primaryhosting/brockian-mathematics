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

theorem bestM_close (Q r s : ℕ) (hr : 0 < r) :
    2 * |((r * bestM Q r s : ℕ) : ℤ) - (s : ℤ) * Q| ≤ (r : ℤ) := by
  have h2r : 0 < 2 * r := by omega
  have hdiv := Nat.div_add_mod (2 * s * Q + r) (2 * r)
  have hmod := Nat.mod_lt (2 * s * Q + r) h2r
  rw [bestM]
  set m := (2 * s * Q + r) / (2 * r) with hm
  set M := (2 * s * Q + r) % (2 * r) with hM
  have hz : (2 : ℤ) * r * m + M = 2 * s * Q + r := by exact_mod_cast hdiv
  have hMz : (M : ℤ) < 2 * r := by exact_mod_cast hmod
  have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
  push_cast
  have habs : (2 : ℤ) * |(r : ℤ) * m - s * Q| = |2 * ((r : ℤ) * m - s * Q)| := by
    rw [abs_mul]; norm_num
  rw [habs, abs_le]
  constructor <;> linarith

