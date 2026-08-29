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

theorem harmonicOscillatorPMap_toFun_ofInjective (f : SchwartzMap ℝ ℂ) :
    harmonicOscillatorPMap
        (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
      = oscillatorCoreMap f := by
  show oscillatorCoreMap.comp
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective).symm.toLinearMap
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
    = oscillatorCoreMap f
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]

/-- The harmonic oscillator has a dense Schwartz domain. -/
