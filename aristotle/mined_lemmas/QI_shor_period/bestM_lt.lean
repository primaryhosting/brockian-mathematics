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

theorem bestM_lt (Q r s : ℕ) (hr : 0 < r) (hs : s < r) (hQ : 0 < Q) (hrQ : r ≤ Q) :
    bestM Q r s < Q := by
  have h2r : 0 < 2 * r := by omega
  have hdiv := Nat.div_add_mod (2 * s * Q + r) (2 * r)
  rw [bestM]
  set m := (2 * s * Q + r) / (2 * r) with hm
  have hle : (2 : ℤ) * r * m ≤ 2 * s * Q + r := by
    have : 2 * r * m ≤ 2 * s * Q + r := by omega
    exact_mod_cast this
  have hsz : (s : ℤ) + 1 ≤ r := by exact_mod_cast hs
  have hQz : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
  have hrQz : (r : ℤ) ≤ Q := by exact_mod_cast hrQ
  have hrz : (1 : ℤ) ≤ r := by exact_mod_cast hr
  by_contra hcon
  push_neg at hcon
  have hmz : (Q : ℤ) ≤ m := by exact_mod_cast hcon
  nlinarith

/-- If `r m` is within `r/2` of `s Q`, then `m/Q` is within `1/(2Q)` of `s/r`. -/
