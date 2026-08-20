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

lemma integrable_wt_exp : Integrable (fun x : ℝ => wt x * Real.exp (-(x/2))) := by
  have hrw : (fun x : ℝ => wt x * Real.exp (-(x/2)))
      = Set.indicator (Ioi (0:ℝ)) (fun x => x * Real.exp (-(x/2))) := by
    funext x
    rcases lt_or_ge 0 x with h | h
    · rw [wt_of_pos h, indicator_of_mem (mem_Ioi.mpr h)]
    · rw [wt_of_nonpos h, indicator_of_notMem (by simpa using h), zero_mul]
  rw [hrw, integrable_indicator_iff measurableSet_Ioi]
  exact intOn_x_exp

/-! ## Integrability on the plane -/

variable {φ : ℝ → ℝ} {C : ℝ}

