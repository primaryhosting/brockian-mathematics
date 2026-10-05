/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
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

namespace Phys

open Finset

/-- Shannon entropy (in nats) of a finite probability distribution `p`. -/

@[simp] lemma shannonEntropy_erasedBit : shannonEntropy erasedBit = 0 := by
  simp [shannonEntropy, erasedBit]

/-- Erasing one bit of memory reduces the Shannon entropy of the memory by exactly
`log 2` (one bit). -/
