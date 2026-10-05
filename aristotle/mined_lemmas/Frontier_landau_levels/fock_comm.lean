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

theorem fock_comm (x : ℕ →₀ ℂ) : fockA (fockB x) = fockB (fockA x) + x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]; abel
  | single n c =>
      cases n with
      | zero => simp
      | succ k =>
          simp only [fockB_single, fockA_single, Nat.add_sub_cancel, ← Finsupp.single_add]
          congr 1
          push_cast
          ring

/-- The creation operator is adjoint to the annihilation operator. -/
