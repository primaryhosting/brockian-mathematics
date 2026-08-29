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

noncomputable def harmonicOscillatorPMap : L2R →ₗ.[ℂ] L2R where
  domain := LinearMap.range schwartzToL2
  toFun := oscillatorCoreMap.comp
    (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective).symm.toLinearMap

