import Mathlib
open Filter Topology
namespace C3.RA6

/-- The sum of two continuous real functions is continuous. -/

theorem cont_mul {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) : Continuous (f * g) :=
  hf.mul hg

/-- The derivative of a sum is the sum of the derivatives. -/
