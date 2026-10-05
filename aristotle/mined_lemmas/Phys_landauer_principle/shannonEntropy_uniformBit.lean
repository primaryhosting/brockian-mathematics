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

@[simp] lemma shannonEntropy_uniformBit : shannonEntropy uniformBit = Real.log 2 := by
  have h2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  simp only [shannonEntropy, uniformBit, Fintype.sum_bool, h2]
  ring

