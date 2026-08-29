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

@[simp] theorem quadraticMulSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    quadraticMulSchwartz f x = (x ^ 2 : ℂ) * f x := by
  rw [quadraticMulSchwartz]
  simpa [smul_eq_mul] using
    SchwartzMap.smulLeftCLM_apply_apply quadratic_hasTemperateGrowth f x

/-- The harmonic-oscillator action on Schwartz functions. -/
