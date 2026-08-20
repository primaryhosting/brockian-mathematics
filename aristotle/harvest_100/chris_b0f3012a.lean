/-
# Simple Zero Shadow
Category: Riemann Program
Target: Riemann.Method.simple_zero_shadow
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Riemann.Method

/-- **Simple Zero Shadow.**
For every natural number `m` with `1 ≤ m` we have `2 * m ≤ m ^ 2 + 1`, with equality
exactly when `m = 1`.  This is Montgomery's `(m - 1) ^ 2 ≥ 0` integrality step which
separates *simple* zeros in the two-thirds argument.

The inequality itself is an instance of Mathlib's `two_mul_le_add_sq`
(`2 * a * b ≤ a ^ 2 + b ^ 2`, here with `b = 1`); the hypothesis `1 ≤ m` is not
needed for either half, but is kept as it appears in the statement to be proved. -/
theorem simple_zero_shadow (m : ℕ) (_hm : 1 ≤ m) :
    2 * m ≤ m ^ 2 + 1 ∧ (2 * m = m ^ 2 + 1 ↔ m = 1) := by
  constructor
  · have h : 2 * m * 1 ≤ m ^ 2 + 1 ^ 2 := two_mul_le_add_sq m 1
    simpa using h
  · constructor
    · intro h
      have hz : (2 * m : ℤ) = (m : ℤ) ^ 2 + 1 := by exact_mod_cast h
      have hsq : ((m : ℤ) - 1) ^ 2 = 0 := by linear_combination -hz
      have : (m : ℤ) - 1 = 0 := by
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
      have : (m : ℤ) = 1 := by linarith
      exact_mod_cast this
    · rintro rfl
      norm_num

#print axioms Riemann.Method.simple_zero_shadow

end Riemann.Method

