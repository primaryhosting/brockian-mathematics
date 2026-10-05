/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace CS

/-- The finset of all binary strings (lists of booleans) of length `n`. -/

def boolLists : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (Finset.univ : Finset Bool).biUnion
      (fun b => (boolLists n).image (fun l => b :: l))

