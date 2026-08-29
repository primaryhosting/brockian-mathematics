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

theorem measProb_nonneg (Q : ℕ) (f : ℕ → β) (m : ℕ) : 0 ≤ measProb Q f m :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The number of `j < Q` in the residue class `k` modulo `r`. -/
