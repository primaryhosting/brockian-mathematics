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
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset SimpleGraph

/-! ## A decidable reformulation of `CliqueFree` -/

/-- `G.CliqueFree n` says: no finset of `n` pairwise-adjacent vertices. -/

def W8 : SimpleGraph (Fin 8) :=
  SimpleGraph.fromRel (fun i j => (i.val + 1) % 8 = j.val ∨ (i.val + 4) % 8 = j.val)

instance : DecidableRel W8.Adj := fun a b => by unfold W8; infer_instance

