import Mathlib
/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

noncomputable section

/-! ## The model -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/

def rowEquiv (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Fin 1 × Fin (n + 1) → Bool) where
  toFun τ := fun p => τ p.2
  invFun σ := fun j => σ (0, j)
  left_inv τ := rfl
  right_inv σ := by
    funext p
    obtain ⟨i, j⟩ := p
    simp [Subsingleton.elim (0 : Fin 1) i]

/-- Reduction of the 2D model on a one-row torus to the exactly solvable 1D ring:
the horizontal bonds contribute the constant factor `exp (K (n+1))`. -/
