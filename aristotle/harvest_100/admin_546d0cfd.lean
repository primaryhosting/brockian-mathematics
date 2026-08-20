/-
# Integrality Shadow
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.integrality_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Integrality Shadow
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.integrality_shadow
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

namespace Zeta23Redux.LinAlg

/-- **Integrality shadow.** For every natural number `m`, `2 * m ≤ m ^ 2 + 1`.
This is Montgomery's integrality step, i.e. the shadow of `(m - 1) ^ 2 ≥ 0`.
The Mathlib lemma `two_mul_le_add_sq : 2 * a * b ≤ a ^ 2 + b ^ 2` closes it
directly (with `b = 1`), after casting to `ℤ`. -/
theorem integrality_shadow (m : ℕ) : 2 * m ≤ m ^ 2 + 1 := by
  have h : (2 : ℤ) * (m : ℤ) * 1 ≤ (m : ℤ) ^ 2 + 1 ^ 2 := two_mul_le_add_sq (m : ℤ) 1
  have h' : (2 * m : ℤ) ≤ ((m ^ 2 + 1 : ℕ) : ℤ) := by push_cast; linarith
  exact_mod_cast h'

/-- Integer form: for `m : ℕ`, `(m : ℤ) ^ 2 ≥ 2 * m - 1`. -/
theorem integrality_shadow_int (m : ℕ) : (2 : ℤ) * (m : ℤ) - 1 ≤ (m : ℤ) ^ 2 := by
  have h := integrality_shadow m
  have : (2 * m : ℤ) ≤ ((m ^ 2 + 1 : ℕ) : ℤ) := by exact_mod_cast h
  push_cast at this
  linarith

end Zeta23Redux.LinAlg

