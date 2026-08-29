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

@[simp] theorem harmonicOscillatorPMap_domain :
    harmonicOscillatorPMap.domain = LinearMap.range schwartzToL2 := rfl

/-- Exact action on an embedded Schwartz function. -/
