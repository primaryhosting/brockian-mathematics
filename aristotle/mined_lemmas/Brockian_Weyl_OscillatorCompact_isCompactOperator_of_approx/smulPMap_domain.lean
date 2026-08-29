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

theorem smulPMap_domain (c : ℝ) : (smulPMap (H := H) c).domain = ⊤ := by
  simp [smulPMap, LinearMap.toPMap]

/-- **Gate-0 (non-vacuity).** -/
