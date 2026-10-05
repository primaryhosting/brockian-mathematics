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

import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Math2

/-! ## The singular plane curves `y ^ n = x ^ (n + 1)` and their normalization -/

/-- The plane affine curve `C_n : y ^ n = x ^ (n + 1)` over a field `k`.
For `n ≥ 2` this curve has a single singular point, at the origin
(for `n = 2` it is the classical cuspidal cubic `y ^ 2 = x ^ 3`). -/

lemma cuspParam_cuspParamInv {k : Type*} [Field k] (n : ℕ) {p : k × k}
    (hp : p ∈ cuspCurve k n) (hx : p.1 ≠ 0) :
    cuspParam k n (cuspParamInv k p) = p := by
  have hp' : p.2 ^ n = p.1 ^ (n + 1) := hp
  have h1 : (p.2 / p.1) ^ n = p.1 := by
    rw [div_pow, hp', pow_succ, mul_comm, mul_div_assoc, div_self (pow_ne_zero n hx), mul_one]
  have h2 : (p.2 / p.1) ^ (n + 1) = p.2 := by
    rw [pow_succ, h1]
    field_simp
  simp only [cuspParamInv, cuspParam, h1, h2]

/-- **Jacobian criterion for `C_n` in characteristic zero:** the gradient of the
defining equation vanishes at a point of the curve exactly at the origin. -/
