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

theorem mem_shiftedRange_iff (T : H →ₗ.[ℂ] H) (z : ℂ) (y : H) :
    y ∈ shiftedRange T z ↔ ∃ v : T.domain, T v - z • (v : H) = y := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [← hv]; rfl⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [← hv]; rfl⟩

/-! ### Closability and symmetry of the closure -/

/-- A densely defined symmetric operator is contained in its adjoint. -/
