/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset SimpleGraph

/-- The Ramsey property `R(3,4) ≤ n`: every simple graph on `n` vertices contains either a
triangle or an independent set of size `4`. -/

def wagner : SimpleGraph (Fin 8) where
  Adj i j := ((i : ℕ) + 1) % 8 = (j : ℕ) ∨ ((j : ℕ) + 1) % 8 = (i : ℕ) ∨ ((i : ℕ) + 4) % 8 = (j : ℕ)
  symm := by
    intro i j h
    revert h
    revert i j
    decide
  loopless := by
    constructor
    intro i
    revert i
    decide

instance : DecidableRel wagner.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The Wagner graph contains no triangle. -/
