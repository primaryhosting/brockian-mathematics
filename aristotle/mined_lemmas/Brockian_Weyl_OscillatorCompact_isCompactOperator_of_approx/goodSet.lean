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

def goodSet (C : ℝ) : Set L2R :=
  {u | ∃ g : SchwartzMap ℝ ℂ, u = schwartzToL2 g ∧ ‖schwartzToL2 g‖ ≤ C ∧ energy g ≤ C}

/-- **The weighted Rellich estimate.** Schwartz states of bounded energy are
uniformly close, in `L²`, to a fixed finite-dimensional space of step
functions. -/
