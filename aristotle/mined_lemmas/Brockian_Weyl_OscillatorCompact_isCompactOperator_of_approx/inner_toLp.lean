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

theorem inner_toLp (f g : SchwartzMap ℝ ℂ) :
    inner ℂ (schwartzToL2 f) (schwartzToL2 g) = ∫ x : ℝ, conj (f x) * g x := by
  have h := SchwartzMap.inner_toL2_toL2_eq f g (volume : Measure ℝ)
  rw [schwartzToL2_apply, schwartzToL2_apply, h]
  simp [RCLike.inner_apply, mul_comm]

/-- Products of Schwartz functions are integrable. -/
