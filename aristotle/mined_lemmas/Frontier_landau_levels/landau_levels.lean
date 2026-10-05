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

theorem landau_levels {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (q B m hbar : ℝ) (a b : V →ₗ[ℂ] V)
    (hcomm : ∀ x, a (b x) = b (a x) + x)
    (hadj : ∀ x y : V, ⟪b x, y⟫_ℂ = ⟪x, a y⟫_ℂ)
    (psi0 : V) (hpsi0 : psi0 ≠ 0) (h0 : a psi0 = 0)
    (H : V →ₗ[ℂ] V)
    (hH : ∀ x, H x = ((hbar * cyclotronFrequency q B m : ℝ) : ℂ) •
      (b (a x) + ((1 / 2 : ℂ)) • x)) :
    ∀ n : ℕ, ladderState b psi0 n ≠ 0 ∧
      H (ladderState b psi0 n)
        = ((landauEnergy hbar (cyclotronFrequency q B m) n : ℝ) : ℂ)
          • ladderState b psi0 n := by
  intro n
  refine ⟨ladderState_ne_zero hcomm hadj hpsi0 h0 n, ?_⟩
  rw [hH, number_apply_ladderState hcomm h0 n]
  rw [landauEnergy]
  push_cast
  module

/-- The Landau Hamiltonian in the concrete Bargmann–Fock model. -/
