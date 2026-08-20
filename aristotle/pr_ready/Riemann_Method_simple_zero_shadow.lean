/-!
# Simple Zero Shadow
Category: Riemann Program
Target: Riemann.Method.simple_zero_shadow
Statement: For every natural number m with 1 <= m, 2 * m <= m^2 + 1 (with equality iff m = 1). This is Montgomery's (m-1)^2 >= 0 integrality step that separates SIMPLE zeros in the two-thirds argument.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
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

/-- **Simple zero shadow** (Montgomery's `(m-1)^2 ≥ 0` integrality step).

For every natural number `m` with `1 ≤ m` we have `2 * m ≤ m ^ 2 + 1`,
with equality precisely when `m = 1`. -/
theorem simple_zero_shadow (m : ℕ) (hm : 1 ≤ m) :
    2 * m ≤ m ^ 2 + 1 ∧ (2 * m = m ^ 2 + 1 ↔ m = 1) := by
  have hsq : m ^ 2 = m * m := sq m
  refine ⟨by nlinarith, ?_, ?_⟩
  · intro h
    by_contra hne
    have h2 : 2 ≤ m := by omega
    nlinarith
  · rintro rfl
    norm_num

end Method
end Riemann

