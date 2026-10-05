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

theorem oscillatorCoreMap_symm (f g : SchwartzMap ℝ ℂ) :
    inner ℂ (oscillatorCoreMap f) (schwartzToL2 g) =
      inner ℂ (schwartzToL2 f) (oscillatorCoreMap g) := by
  rw [oscillatorCoreMap_expanded, oscillatorCoreMap_expanded,
    inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
    kinetic_symm f g, quadraticMul_symm f g]

/-- The concrete minimal harmonic oscillator is symmetric. -/
