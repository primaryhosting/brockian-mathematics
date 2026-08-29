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

def EssentiallySelfAdjoint (T : H →ₗ.[ℂ] H) : Prop :=
  deficiencySpace T Complex.I = ⊥ ∧ deficiencySpace T (-Complex.I) = ⊥

end Adjoint

/-- **The everywhere-defined real-scalar operator** `x ↦ (c : ℝ) • x`. -/
