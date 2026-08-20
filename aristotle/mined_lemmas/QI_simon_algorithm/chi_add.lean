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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace QI

/-! ## Basic setup: the group `(ZMod 2)^n` -/

/-- The domain of Simon's problem: bit strings of length `n`, viewed as the
elementary abelian group `(ZMod 2)^n` under bitwise XOR (= addition). -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}


lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  rcases zmod2_cases a with ha | ha <;> rcases zmod2_cases b with hb | hb <;>
    simp [ha, hb, h]

/-- The amplitude of the basis state `|y⟩|z⟩` in the state
`(1/2^n) ∑_{x,y} (-1)^{x·y} |y⟩|f(x)⟩`, i.e. the state obtained from `|0⟩|0⟩` by
Hadamard transforming the first register, applying one oracle query to `f`, and
Hadamard transforming the first register again. -/
