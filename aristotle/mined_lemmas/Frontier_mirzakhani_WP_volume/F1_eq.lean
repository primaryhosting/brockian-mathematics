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

theorem F1_eq (t : ℝ) : F1 t = t ^ 2 / 2 + 2 * π ^ 2 / 3 := by
  rcases le_total 0 t with h | h
  · exact F1_eq_of_nonneg h
  · have h' : (0:ℝ) ≤ -t := by linarith
    have hval := F1_eq_of_nonneg h'
    rw [F1_neg] at hval
    rw [hval]; ring

/-- **Mirzakhani's second integral transform.**
`∫₀^∞ x³ H(x,t) dx = t⁴/4 + 2π²t² + 28π⁴/15`. -/
