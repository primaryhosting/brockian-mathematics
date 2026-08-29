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

theorem inner_ladderState_self {a b : V →ₗ[ℂ] V}
    (hcomm : ∀ x, a (b x) = b (a x) + x)
    (hadj : ∀ x y : V, ⟪b x, y⟫_ℂ = ⟪x, a y⟫_ℂ)
    {psi0 : V} (h0 : a psi0 = 0) (n : ℕ) :
    ⟪ladderState b psi0 n, ladderState b psi0 n⟫_ℂ
      = (n ! : ℂ) * ⟪psi0, psi0⟫_ℂ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have key : ⟪ladderState b psi0 (n + 1), ladderState b psi0 (n + 1)⟫_ℂ
          = ((n : ℂ) + 1) * ⟪ladderState b psi0 n, ladderState b psi0 n⟫_ℂ := by
        rw [ladderState_succ, hadj, hcomm, inner_add_right,
          number_apply_ladderState hcomm h0 n, inner_smul_right]
        ring
      rw [key, ih, Nat.factorial_succ]
      push_cast
      ring

/-- Each ladder state is a genuine (nonzero) state. -/
