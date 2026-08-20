import Mathlib
open Filter Topology
namespace C3.RA6

/-- The sum of two continuous real functions is continuous. -/

theorem deriv_add (f g : ℝ → ℝ) (x : ℝ) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f + g) x = deriv f x + deriv g x :=
  _root_.deriv_add hf hg

end C3.RA6

