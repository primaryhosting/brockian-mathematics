import Mathlib
import RequestProject.Kernel
import RequestProject.TwoDim

/-!
# Weil–Petersson volume polynomials in low complexity

We record the Weil–Petersson volume polynomials `V_{0,3}`, `V_{0,4}` and `V_{0,5}`, the
right-hand sides of Mirzakhani's recursion in the cases `(g,n) = (0,4)` and `(0,5)`, and
verify the recursion in both cases, together with the fact that the recursion determines
the volume polynomial.
-/

open scoped BigOperators Real
open MeasureTheory Set Real

namespace Frontier

set_option maxHeartbeats 1000000

/-! ## The volume polynomials -/

/-- `V_{0,3} ≡ 1`: the moduli space of pairs of pants is a point. -/

lemma hasSum_inv_pow_four : HasSum (fun n : ℕ => 1 / ((n:ℝ)+1) ^ 4) (π^4/90) := by
  have h := hasSum_zeta_four
  rw [← hasSum_nat_add_iff' 1] at h
  simpa using h

/-- The alternating Euler sum `η(2) = π²/12`. -/
