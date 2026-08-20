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

theorem cos_two_pi_div_five : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  have h : (2 * Real.pi / 5) = 2 * (Real.pi / 5) := by ring
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

