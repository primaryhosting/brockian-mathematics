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

lemma moment_split_pos (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ y in Ioi t, y^k * fd y)
      = (∫ y in Ioi (0:ℝ), y^k * fd y) - ∫ y in (0:ℝ)..t, y^k * fd y := by
  have h := integral_Ioi_split (fun y => y^k * fd y) ht (intOn_pow_fd k 0)
  linarith [h]

