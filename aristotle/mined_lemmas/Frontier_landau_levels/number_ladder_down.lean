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

theorem number_ladder_down (A B : V →ₗ[ℂ] V)
    (hcomm : ∀ x : V, A (B x) - B (A x) = x)
    {v : V} {μ : ℂ} (h : B (A v) = μ • v) :
    B (A (A v)) = (μ - 1) • A v := by
  have h1 := hcomm (A v)
  have h2 : A (B (A v)) = μ • A v := by rw [h, map_smul]
  rw [h2] at h1
  have h4 : μ • A v = A v + B (A (A v)) := sub_eq_iff_eq_add.mp h1
  have : B (A (A v)) = μ • A v - A v := by
    rw [h4]; abel
  rw [this, sub_smul, one_smul]

/-- Iterated lowering: `Aⁿ v` is an eigenvector of `N = B ∘ A` with eigenvalue `μ - n`
(or is zero). -/
