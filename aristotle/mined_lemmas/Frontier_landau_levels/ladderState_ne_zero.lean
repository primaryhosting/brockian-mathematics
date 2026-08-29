import Mathlib
import RequestProject.Fock
/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open scoped InnerProductSpace

/-- The cyclotron frequency `ω_c = q B / m` of a particle of charge `q` and mass `m`
in a uniform magnetic field of strength `B`. -/

theorem ladderState_ne_zero {a b : V →ₗ[ℂ] V}
    (hcomm : ∀ x, a (b x) = b (a x) + x)
    (hadj : ∀ x y : V, ⟪b x, y⟫_ℂ = ⟪x, a y⟫_ℂ)
    {psi0 : V} (hpsi0 : psi0 ≠ 0) (h0 : a psi0 = 0) (n : ℕ) :
    ladderState b psi0 n ≠ 0 := by
  intro hzero
  have h := inner_ladderState_self hcomm hadj h0 n
  rw [hzero] at h
  simp only [inner_zero_left] at h
  have hfac : (n ! : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have : ⟪psi0, psi0⟫_ℂ = 0 := by
    rcases mul_eq_zero.mp h.symm with h1 | h2
    · exact absurd h1 hfac
    · exact h2
  exact hpsi0 (inner_self_eq_zero.mp this)

/--
**Landau levels.**

A charged particle of charge `q` and mass `m` in a uniform magnetic field `B` has, after
separation of variables in the Landau gauge, a Hamiltonian of harmonic-oscillator form
`H = ℏ ω_c (a† a + 1/2)` with cyclotron frequency `ω_c = q B / m`, where the ladder
operators satisfy the canonical commutation relation `[a, a†] = 1` and `a†` is the adjoint
of `a`.

Given a nonzero lowest state `ψ₀` annihilated by `a`, the states `ψ_n = (a†)ⁿ ψ₀` are
nonzero eigenstates of `H` with the equally spaced Landau energies
`E_n = ℏ ω_c (n + 1/2)`.
-/
