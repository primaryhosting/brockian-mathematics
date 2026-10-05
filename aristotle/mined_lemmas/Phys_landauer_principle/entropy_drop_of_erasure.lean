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

lemma entropy_drop_of_erasure :
    shannonEntropy uniformBit - shannonEntropy erasedBit = Real.log 2 := by
  simp

/-- **Gibbs' inequality for one bit**: no distribution on a two-state memory carries
more than `log 2` of entropy, so `log 2` is exactly the information content of one bit. -/
