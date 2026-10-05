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

theorem shiftedInverse_spec (S : H →ₗ.[ℂ] H) (z : ℂ) (hS : IsSymmetric S)
    (hz : |z.im| = 1) (hsurj : ∀ y : H, ∃ v : S.domain, S v - z • (v : H) = y) :
    RightResolvent S z (shiftedInverse S z hS hz hsurj) := by
  intro x
  have h1 := (hsurj x).choose_spec
  have hmem : (shiftedInverse S z hS hz hsurj) x ∈ S.domain := ((hsurj x).choose).2
  refine ⟨hmem, ?_⟩
  have : (⟨(shiftedInverse S z hS hz hsurj) x, hmem⟩ : S.domain) = (hsurj x).choose :=
    Subtype.ext rfl
  rw [this]
  exact h1

omit [CompleteSpace H] in
