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

lemma amplitude_eq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    amplitude f = 1 - 2 * (numTrue f : ℝ) / 2 ^ n := by
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  rw [amplitude, sum_sign]
  field_simp

/-- Sign `(-1)^{x·y}` of the bitwise inner product of two `n`-bit strings. -/
