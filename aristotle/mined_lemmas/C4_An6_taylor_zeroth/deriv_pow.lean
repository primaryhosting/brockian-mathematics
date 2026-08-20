import Mathlib
open Filter Topology
namespace C4.An6


theorem deriv_pow (n : ℕ) (x : ℝ) : deriv (fun y => y ^ n) x = n * x ^ (n - 1) := by
  simp

