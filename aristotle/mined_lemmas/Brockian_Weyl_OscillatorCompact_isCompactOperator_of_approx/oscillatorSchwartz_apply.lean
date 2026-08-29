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

@[simp] theorem oscillatorSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    oscillatorSchwartz f x = -deriv (deriv f) x + (x ^ 2 : ℂ) * f x := by
  simp [oscillatorSchwartz, D2_apply]

/-- The harmonic-oscillator core action, valued in `L2(R)`. -/
