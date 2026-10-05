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

theorem fock_landau_spectrum (hbar omegac : ℝ) (hbar_pos : 0 < hbar) (homega_pos : 0 < omegac)
    (E : ℂ) :
    (∃ v : ℕ →₀ ℂ, v ≠ 0 ∧ fockH hbar omegac v = E • v) ↔
      ∃ n : ℕ, E = ((hbar * omegac : ℝ) : ℂ) * ((n : ℂ) + 1 / 2) := by
  constructor
  · rintro ⟨v, hv, hEv⟩
    exact Frontier.landau_levels aOp adagOp
      (fun x y => by rw [inner_eq_finner, inner_eq_finner]; exact fock_adjoint x y)
      fock_ccr hbar omegac hbar_pos homega_pos (fockH hbar omegac)
      (fockH_apply hbar omegac) hv hEv
  · rintro ⟨n, rfl⟩
    refine ⟨Finsupp.single n (1 : ℂ), single_ne_zero n, ?_⟩
    rw [fockH_apply, number_eigenvector n]
    module

/-- **Consistency of the Landau-level hypotheses.**  There is an inner product space carrying
operators `a`, `a†` which are mutually adjoint and satisfy the canonical commutation
relation `[a, a†] = 1`; hence `Frontier.landau_levels` is not vacuous. -/
