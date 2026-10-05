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

noncomputable def stepLp (c : ℕ → ℂ) (Rr hh : ℝ) (n : ℕ) : L2R :=
  ∑ j ∈ Finset.range n, c j • cellLp Rr hh j

