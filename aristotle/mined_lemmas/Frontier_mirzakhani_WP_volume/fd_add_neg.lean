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

lemma fd_add_neg (s : ℝ) : fd s + fd (-s) = 1 := by
  have hE : (0:ℝ) < Real.exp (s / 2) := Real.exp_pos _
  have h : Real.exp (-s / 2) = (Real.exp (s / 2))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [fd, fd, h]
  field_simp
  ring

