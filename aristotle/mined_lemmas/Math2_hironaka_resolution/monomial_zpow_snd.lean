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

lemma monomial_zpow_snd {x y : k} (hy : y ≠ 0) {a b : ℕ} {u v : ℤ}
    (hxy : y ^ (a : ℤ) = x ^ (b : ℤ)) (huv : u * (a : ℤ) + v * (b : ℤ) = 1) :
    (x ^ u * y ^ v) ^ (b : ℤ) = y := by
  have e1 : x ^ (u * (b : ℤ)) = y ^ ((a : ℤ) * u) := by
    rw [mul_comm u (b : ℤ), zpow_mul, ← hxy, ← zpow_mul]
  calc (x ^ u * y ^ v) ^ (b : ℤ) = x ^ (u * (b : ℤ)) * y ^ (v * (b : ℤ)) := by
        rw [mul_zpow, ← zpow_mul, ← zpow_mul]
    _ = y ^ ((a : ℤ) * u) * y ^ (v * (b : ℤ)) := by rw [e1]
    _ = y ^ ((a : ℤ) * u + v * (b : ℤ)) := (zpow_add₀ hy _ _).symm
    _ = y := by rw [show (a : ℤ) * u + v * (b : ℤ) = 1 by linarith, zpow_one]

/-- The parametrization lands on the curve. -/
