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

noncomputable def shiftedInverse (S : H →ₗ.[ℂ] H) (z : ℂ) (hS : IsSymmetric S)
    (hz : |z.im| = 1) (hsurj : ∀ y : H, ∃ v : S.domain, S v - z • (v : H) = y) :
    H →L[ℂ] H := by
  classical
  refine LinearMap.mkContinuous
    { toFun := fun y => (((hsurj y).choose : S.domain) : H)
      map_add' := ?_
      map_smul' := ?_ } 1 ?_
  · intro y₁ y₂
    have h1 := (hsurj y₁).choose_spec
    have h2 := (hsurj y₂).choose_spec
    have h3 := (hsurj (y₁ + y₂)).choose_spec
    have heq : (hsurj (y₁ + y₂)).choose = (hsurj y₁).choose + (hsurj y₂).choose := by
      refine eq_of_shifted_eq hS hz ?_
      have hcoe : (((hsurj y₁).choose + (hsurj y₂).choose : S.domain) : H)
          = ((hsurj y₁).choose : H) + ((hsurj y₂).choose : H) := rfl
      have hR : S ((hsurj y₁).choose + (hsurj y₂).choose)
            - z • (((hsurj y₁).choose + (hsurj y₂).choose : S.domain) : H) = y₁ + y₂ := by
        rw [LinearPMap.map_add, hcoe, smul_add]
        have hsplit : S (hsurj y₁).choose + S (hsurj y₂).choose
            - (z • ((hsurj y₁).choose : H) + z • ((hsurj y₂).choose : H))
            = (S (hsurj y₁).choose - z • ((hsurj y₁).choose : H))
              + (S (hsurj y₂).choose - z • ((hsurj y₂).choose : H)) := by abel
        rw [hsplit, h1, h2]
      rw [h3, hR]
    rw [heq]; rfl
  · intro c y
    have h1 := (hsurj y).choose_spec
    have h2 := (hsurj (c • y)).choose_spec
    have heq : (hsurj (c • y)).choose = c • (hsurj y).choose := by
      refine eq_of_shifted_eq hS hz ?_
      have hcoe : ((c • (hsurj y).choose : S.domain) : H) = c • ((hsurj y).choose : H) := rfl
      have hR : S (c • (hsurj y).choose) - z • ((c • (hsurj y).choose : S.domain) : H)
          = c • y := by
        rw [LinearPMap.map_smul, hcoe, smul_comm z c, ← smul_sub, h1]
      rw [h2, hR]
    rw [heq]; rfl
  · intro y
    have h1 := (hsurj y).choose_spec
    have h := norm_le_norm_shifted hS hz (hsurj y).choose
    rw [h1] at h
    simpa using h

omit [CompleteSpace H] in
