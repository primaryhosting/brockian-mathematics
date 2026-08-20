/-
# Rank Trace C 3 Shadow
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Method.rank_trace_c3_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Rank Trace C 3 Shadow
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Method.rank_trace_c3_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann
namespace Method

/-- The `c = 3` scalar shadow of the rank-trace inequality:
for every real `x`, `3 * x - 9 / 4 ≤ x ^ 2`, equivalently `(x - 3/2) ^ 2 ≥ 0`.

The proof is an instance of the Mathlib lemma `two_mul_le_add_sq :
2 * a * b ≤ a ^ 2 + b ^ 2` with `a = x`, `b = 3 / 2`. -/
theorem rank_trace_c3_shadow (x : ℝ) : 3 * x - 9 / 4 ≤ x ^ 2 := by
  have h : 2 * x * (3 / 2 : ℝ) ≤ x ^ 2 + (3 / 2 : ℝ) ^ 2 := two_mul_le_add_sq x (3 / 2)
  linarith

/-- Equivalent square form: `(x - 3/2) ^ 2 ≥ 0`. -/
theorem rank_trace_c3_shadow_sq (x : ℝ) : 0 ≤ (x - 3 / 2) ^ 2 := sq_nonneg _

end Method
end Riemann

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

