/-
# Landau Levels — a concrete model
A Fock-space realization of the ladder-operator hypotheses used in
`Frontier.landau_levels`, showing that they are consistent and that every
level `ℏ ω_c (n + 1/2)` really occurs.
-/

import Mathlib
import RequestProject.LandauLevels

namespace Frontier.Fock

/-! ### The inner product on finitely supported sequences -/

/-- The Fock inner product on finitely supported complex sequences. -/

theorem number_eigenvalue_nonneg (A B : V →ₗ[ℂ] V)
    (hadj : ∀ x y : V, ⟪A x, y⟫_ℂ = ⟪x, B y⟫_ℂ)
    {v : V} (hv : v ≠ 0) {μ : ℂ} (h : B (A v) = μ • v) :
    ∃ r : ℝ, 0 ≤ r ∧ μ = (r : ℂ) := by
  have hvv : (‖v‖ : ℂ) ^ 2 ≠ 0 := by
    simpa [pow_eq_zero_iff] using (norm_ne_zero_iff.mpr hv)
  have key : ((‖A v‖ : ℂ)) ^ 2 = μ * ((‖v‖ : ℂ)) ^ 2 := by
    have h1 : ⟪A v, A v⟫_ℂ = ⟪v, B (A v)⟫_ℂ := hadj _ _
    rw [h, inner_smul_right] at h1
    rw [inner_self_eq_norm_sq_to_K] at h1
    rw [inner_self_eq_norm_sq_to_K] at h1
    exact_mod_cast h1
  refine ⟨‖A v‖ ^ 2 / ‖v‖ ^ 2, by positivity, ?_⟩
  have : μ = ((‖A v‖ : ℂ)) ^ 2 / ((‖v‖ : ℂ)) ^ 2 := by
    rw [key, mul_div_assoc, div_self hvv, mul_one]
  rw [this]
  push_cast
  ring

/-- Lowering step: if `[A, B] = 1` and `v` is an eigenvector of `N = B ∘ A` with eigenvalue `μ`,
then `A v` is an eigenvector of `N` with eigenvalue `μ - 1` (or is zero). -/
