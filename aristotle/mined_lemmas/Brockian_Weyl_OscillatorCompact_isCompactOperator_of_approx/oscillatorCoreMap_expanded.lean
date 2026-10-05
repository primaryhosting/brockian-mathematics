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

theorem oscillatorCoreMap_expanded (f : SchwartzMap ℝ ℂ) :
    oscillatorCoreMap f =
      -(schwartzToL2 (D2 f)) + schwartzToL2 (quadraticMulSchwartz f) := by
  show schwartzToL2 (oscillatorSchwartz f) = _
  rw [oscillatorSchwartz]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, map_add, map_neg]

/-- The minimal harmonic oscillator `-d^2/dx^2 + x^2` on the Schwartz core. -/
