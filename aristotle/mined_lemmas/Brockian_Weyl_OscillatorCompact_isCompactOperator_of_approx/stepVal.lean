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

noncomputable def stepVal (c : ℕ → ℂ) (Rr hh : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, Set.indicator (cellSet Rr hh j) (fun _ => c j) x

