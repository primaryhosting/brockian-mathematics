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

noncomputable def oscillatorCoreMap : SchwartzMap ℝ ℂ →ₗ[ℂ] L2R :=
  schwartzToL2.comp oscillatorSchwartz.toLinearMap

