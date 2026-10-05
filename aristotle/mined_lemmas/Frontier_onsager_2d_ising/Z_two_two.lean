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

lemma Z_two_two (β J : ℝ) : Z 2 2 β J = 12 + 4 * Real.cosh (8 * β * J) := by
  rw [Z, ← Equiv.sum_comp cfg22 (fun σ => Real.exp (-β * energy J σ))]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, energy, Fin.sum_univ_two, cfg22,
    Equiv.coe_fn_mk, spin, nextIdx]
  norm_num
  rw [Real.cosh_eq, show (8:ℝ) * β * J = β * (J * 8) by ring]
  ring

/-- The Onsager critical point: `sinh (2βJ) = 1` holds exactly at `β = log (1 + √2) / (2J)`. -/
