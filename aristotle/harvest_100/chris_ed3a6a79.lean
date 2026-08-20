-- # Integrality Shadow
-- Category: Zeta-23 §3 Linear Algebra (re-derivation)
-- Target: Zeta23Redux.LinAlg.integrality_shadow
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)
-- (The required header appears verbatim as a module docstring immediately after
--  the `import`, since Lean 4 requires `import` to precede all commands.)

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Redux.LinAlg

/-- Montgomery's integrality step, natural-number form: `2 * m ≤ m ^ 2 + 1`.
It follows from `(m - 1) ^ 2 ≥ 0`, i.e. from Mathlib's
`two_mul_le_add_sq : 2 * a * b ≤ a ^ 2 + b ^ 2` applied with `b = 1`. -/
theorem integrality_shadow_nat (m : ℕ) : 2 * m ≤ m ^ 2 + 1 := by
  have h : (2 : ℤ) * (m : ℤ) * 1 ≤ (m : ℤ) ^ 2 + 1 ^ 2 := two_mul_le_add_sq (m : ℤ) 1
  have h' : (2 * m : ℤ) ≤ ((m ^ 2 + 1 : ℕ) : ℤ) := by push_cast; linarith
  exact_mod_cast h'

/-- Montgomery's integrality step, integer form: `(m : ℤ) ^ 2 ≥ 2 * m - 1`. -/
theorem integrality_shadow_int (m : ℕ) : ((m : ℤ)) ^ 2 ≥ 2 * (m : ℤ) - 1 := by
  have h : (2 : ℤ) * (m : ℤ) * 1 ≤ (m : ℤ) ^ 2 + 1 ^ 2 := two_mul_le_add_sq (m : ℤ) 1
  linarith

/-- **Integrality shadow.** For every natural number `m` we have `2 * m ≤ m ^ 2 + 1`,
equivalently `(m : ℤ) ^ 2 ≥ 2 * m - 1`.  This is Montgomery's integrality step,
coming from `(m - 1) ^ 2 ≥ 0`. -/
theorem integrality_shadow :
    ∀ m : ℕ, 2 * m ≤ m ^ 2 + 1 ∧ ((m : ℤ)) ^ 2 ≥ 2 * (m : ℤ) - 1 :=
  fun m => ⟨integrality_shadow_nat m, integrality_shadow_int m⟩

end Zeta23Redux.LinAlg

