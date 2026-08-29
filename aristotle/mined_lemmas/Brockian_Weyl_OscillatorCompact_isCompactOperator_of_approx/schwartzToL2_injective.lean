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

theorem schwartzToL2_injective : Function.Injective schwartzToL2 :=
  SchwartzMap.injective_toLp 2 (volume : Measure ℝ)

