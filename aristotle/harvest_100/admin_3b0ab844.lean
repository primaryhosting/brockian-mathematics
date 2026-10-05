import Mathlib

/-!
# Simple Zero Shadow
Category: Riemann Program
Target: Riemann.Method.simple_zero_shadow
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

namespace Riemann
namespace Method

/-- Montgomery's integrality step `(m-1)^2 ≥ 0`: for every natural number `m ≥ 1`
we have `2 * m ≤ m ^ 2 + 1`, with equality exactly when `m = 1`. -/
theorem simple_zero_shadow (m : ℕ) (hm : 1 ≤ m) :
    2 * m ≤ m ^ 2 + 1 ∧ (2 * m = m ^ 2 + 1 ↔ m = 1) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k + 1 := ⟨m - 1, by omega⟩
  constructor
  -- The inequality is the AM-GM instance `two_mul_le_add_sq` from Mathlib.
  · simpa using two_mul_le_add_sq (k + 1) 1
  · constructor
    · intro h
      have : k = 0 := by nlinarith [sq_nonneg k]
      omega
    · intro h
      have hk : k = 0 := by omega
      subst hk
      norm_num

end Method
end Riemann

