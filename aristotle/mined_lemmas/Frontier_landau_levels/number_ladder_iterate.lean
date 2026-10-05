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

theorem number_ladder_iterate (A B : V →ₗ[ℂ] V)
    (hcomm : ∀ x : V, A (B x) - B (A x) = x)
    {v : V} {μ : ℂ} (h : B (A v) = μ • v) (n : ℕ) :
    B (A ((A : V → V)^[n] v)) = (μ - n) • (A : V → V)^[n] v := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      have := number_ladder_down A B hcomm ih
      rw [Function.iterate_succ_apply' (f := (A : V → V))]
      rw [this]
      push_cast
      ring_nf

/-- **Quantization of the number operator.**  If `B` is the adjoint of `A` and `[A, B] = 1`,
then every eigenvalue of the number operator `N = B ∘ A` is a natural number. -/
