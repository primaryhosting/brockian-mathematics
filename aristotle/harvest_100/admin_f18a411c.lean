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

-- (Lean 4 requires `import` lines to precede any module docstring, so the
-- requested header comment appears immediately after the import.)
import Mathlib

/-!
# Integrality Shadow
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.integrality_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Zeta23Redux
namespace LinAlg

/-- **Integrality shadow.** For every natural number `m`, `2 * m ≤ m ^ 2 + 1`.
This is Montgomery's integrality step, i.e. the scalar shadow of `(m - 1) ^ 2 ≥ 0`,
whose matrix analogue is Lemma 3.2.

It is the case `b = 1` of the Mathlib lemma `two_mul_le_add_sq : 2 * a * b ≤ a ^ 2 + b ^ 2`. -/
theorem integrality_shadow (m : ℕ) : 2 * m ≤ m ^ 2 + 1 := by
  simpa using two_mul_le_add_sq (m : ℕ) 1

/-- The equivalent integer form of `integrality_shadow`: `(m : ℤ) ^ 2 ≥ 2 * m - 1`. -/
theorem integrality_shadow_int (m : ℕ) : ((m : ℤ)) ^ 2 ≥ 2 * (m : ℤ) - 1 := by
  have h : (2 * m : ℕ) ≤ m ^ 2 + 1 := integrality_shadow m
  have h' : (2 * (m : ℤ)) ≤ (m : ℤ) ^ 2 + 1 := by exact_mod_cast h
  linarith

end LinAlg
end Zeta23Redux

