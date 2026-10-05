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

theorem energy_nonneg (g : SchwartzMap ℝ ℂ) : 0 ≤ energy g :=
  add_nonneg (integral_nonneg fun _ => by positivity)
    (integral_nonneg fun _ => by positivity)

/-- The `L²`-image of the Schwartz functions of norm and energy at most `C`. -/
