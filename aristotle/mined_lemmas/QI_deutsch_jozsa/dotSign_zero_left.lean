/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

namespace QI

open Finset

/-- The number of inputs `x` on which the oracle `f` returns `true`. -/

lemma dotSign_zero_left {n : ℕ} (y : Fin n → Bool) : dotSign (fun _ => false) y = 1 := by
  simp [dotSign]

/-- After the first Hadamard layer the register is in the uniform superposition. -/
