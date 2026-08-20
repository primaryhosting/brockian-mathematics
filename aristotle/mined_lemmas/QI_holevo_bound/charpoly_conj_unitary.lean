import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
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

namespace QI

open Finset

/-! ### Classical entropies -/

/-- Shannon entropy of a probability vector, in nats. -/

lemma charpoly_conj_unitary (U A : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    (U * A * Uᴴ).charpoly = A.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

