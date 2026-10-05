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

theorem number_apply_ladderState {a b : V →ₗ[ℂ] V}
    (hcomm : ∀ x, a (b x) = b (a x) + x) {psi0 : V} (h0 : a psi0 = 0) (n : ℕ) :
    b (a (ladderState b psi0 n)) = (n : ℂ) • ladderState b psi0 n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
      rw [ladderState_succ, hcomm, map_add, ih, map_smul]
      push_cast
      module

/-- The squared norm of the `n`-th ladder state is `n!` times that of the ground state. -/
