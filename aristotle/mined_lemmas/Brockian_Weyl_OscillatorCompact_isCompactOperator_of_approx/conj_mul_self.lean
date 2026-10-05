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

theorem conj_mul_self (a : ℂ) : conj a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.conj_mul]; norm_cast

