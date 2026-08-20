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

namespace Math2

variable (k : Type*) [Field k]

/-- The affine plane curve `C_{a,b} : y^a = x^b` over a field `k`.
For `a, b ≥ 2` coprime this is the standard quasi-homogeneous plane curve singularity
(for `(a,b) = (2,3)` it is the cuspidal cubic `y² = x³`). -/

lemma monomial_zpow_fst {x y : k} (hx : x ≠ 0) {a b : ℕ} {u v : ℤ}
    (hxy : y ^ (a : ℤ) = x ^ (b : ℤ)) (huv : u * (a : ℤ) + v * (b : ℤ) = 1) :
    (x ^ u * y ^ v) ^ (a : ℤ) = x := by
  have e1 : y ^ (v * (a : ℤ)) = x ^ ((b : ℤ) * v) := by
    rw [mul_comm v (a : ℤ), zpow_mul, hxy, ← zpow_mul]
  calc (x ^ u * y ^ v) ^ (a : ℤ) = x ^ (u * (a : ℤ)) * y ^ (v * (a : ℤ)) := by
        rw [mul_zpow, ← zpow_mul, ← zpow_mul]
    _ = x ^ (u * (a : ℤ)) * x ^ ((b : ℤ) * v) := by rw [e1]
    _ = x ^ (u * (a : ℤ) + (b : ℤ) * v) := (zpow_add₀ hx _ _).symm
    _ = x := by rw [show u * (a : ℤ) + (b : ℤ) * v = 1 by linarith, zpow_one]

/-- The `b`-th power of the Laurent monomial `x^u y^v` on the curve is `y`. -/
