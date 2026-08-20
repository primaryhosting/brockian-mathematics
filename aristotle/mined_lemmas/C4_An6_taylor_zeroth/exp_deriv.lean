import Mathlib
open Filter Topology
namespace C4.An6


theorem exp_deriv (x : ℝ) : deriv Real.exp x = Real.exp x := by
  rw [Real.deriv_exp]

end C4.An6

