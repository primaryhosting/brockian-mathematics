import Mathlib
open Filter Topology
namespace C3.RA6

/-- The sum of two continuous real functions is continuous. -/

theorem cont_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) : Continuous (f + g) :=
  hf.add hg

/-- The product of two continuous real functions is continuous. -/
