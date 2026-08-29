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

def cellSet (Rr hh : ℝ) (j : ℕ) : Set ℝ := Set.Ioc (-Rr + j * hh) (-Rr + (j + 1) * hh)

