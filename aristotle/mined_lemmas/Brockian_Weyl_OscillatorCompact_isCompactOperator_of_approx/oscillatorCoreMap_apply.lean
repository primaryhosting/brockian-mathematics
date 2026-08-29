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

@[simp] theorem oscillatorCoreMap_apply (f : SchwartzMap ℝ ℂ) :
    oscillatorCoreMap f = schwartzToL2 (oscillatorSchwartz f) := rfl

