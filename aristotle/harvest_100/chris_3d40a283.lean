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
# Integrality Shadow
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.integrality_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Redux.LinAlg

/-- **Integrality shadow.** For every natural number `m`, `2 * m ≤ m ^ 2 + 1`,
equivalently `(m : ℤ) ^ 2 ≥ 2 * m - 1`.  This is Montgomery's integrality step,
i.e. the expansion of `(m - 1) ^ 2 ≥ 0`; its matrix analogue is Lemma 3.2.

Both halves follow from the Mathlib lemma `two_mul_le_add_sq : 2 * a * b ≤ a ^ 2 + b ^ 2`
specialized at `b = 1`. -/
theorem integrality_shadow (m : ℕ) :
    2 * m ≤ m ^ 2 + 1 ∧ 2 * (m : ℤ) - 1 ≤ (m : ℤ) ^ 2 := by
  refine ⟨by simpa using two_mul_le_add_sq (m : ℕ) 1, ?_⟩
  have := two_mul_le_add_sq (m : ℤ) 1
  simp only [mul_one, one_pow] at this
  linarith

end Zeta23Redux.LinAlg

