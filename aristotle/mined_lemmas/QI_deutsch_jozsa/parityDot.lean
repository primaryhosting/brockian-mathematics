/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

/-- The number of inputs on which `f` takes the value `true`. -/

def parityDot {n : ℕ} (x y : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => (x i && y i) = true).card

/-- The amplitude of the basis state `y` in the final state of the Deutsch–Jozsa
circuit: apply Hadamards, one phase query to `f`, and Hadamards again. -/
