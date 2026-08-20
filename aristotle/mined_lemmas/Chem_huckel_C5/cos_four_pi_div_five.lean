import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
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

namespace Chem

open Matrix Complex

/-- Adjacency matrix of the cycle graph `C₅` (the Hückel matrix of the cyclopentadienyl
π-system in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`). -/

theorem cos_four_pi_div_five : Real.cos (4 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4 := by
  have h : (4 * Real.pi / 5) = Real.pi - Real.pi / 5 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_five]
  ring

/-- **Hückel theory for the cyclopentadienyl π-system.**  A complex number `μ` is an
eigenvalue of the adjacency (Hückel) matrix of the cycle graph `C₅` if and only if
`μ = 2 cos (2πk/5)` for some `k ∈ {0,1,2,3,4}`. -/
