/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

theorem quadraticMul_symm (f g : SchwartzMap ℝ ℂ) :
    inner ℂ (schwartzToL2 (quadraticMulSchwartz f)) (schwartzToL2 g) =
      inner ℂ (schwartzToL2 f) (schwartzToL2 (quadraticMulSchwartz g)) := by
  rw [inner_toLp, inner_toLp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [quadraticMulSchwartz_apply, map_mul, map_pow, Complex.conj_ofReal]
  ring

/-- The full oscillator action is symmetric on Schwartz functions. -/
