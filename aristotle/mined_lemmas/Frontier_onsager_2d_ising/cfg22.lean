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

/-- The real value of an Ising spin: `true ↦ +1`, `false ↦ -1`. -/

def cfg22 : (Bool × Bool × Bool × Bool) ≃ (Fin 2 × Fin 2 → Bool) where
  toFun b p :=
    if p = (0, 0) then b.1 else if p = (0, 1) then b.2.1 else if p = (1, 0) then b.2.2.1
    else b.2.2.2
  invFun σ := (σ (0, 0), σ (0, 1), σ (1, 0), σ (1, 1))
  left_inv b := by rfl
  right_inv σ := by funext p; fin_cases p <;> rfl

/-- Exact finite-size evaluation: on the `2 × 2` torus (where every bond is doubled)
`Z = 12 + 4 cosh (8βJ)`. -/
