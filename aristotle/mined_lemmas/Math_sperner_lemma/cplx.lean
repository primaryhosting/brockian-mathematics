import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-! ## Auxiliary counting lemmas -/

/-- Parity translated into `ZMod 2`. -/

def cplx : Finset (Finset (Fin 3)) := {∅, {0}, {1}, {2}, {0, 1}, {1, 2}}

/-- A Sperner colouring of the subdivided segment. -/
