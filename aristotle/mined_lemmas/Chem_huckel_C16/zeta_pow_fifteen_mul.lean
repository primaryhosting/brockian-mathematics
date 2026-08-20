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

set_option grind.warning false

namespace Chem

/-- A primitive 16-th root of unity. -/

lemma zeta_pow_fifteen_mul (k : ℕ) : zeta ^ (15 * k) = (zeta ^ k)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← pow_add, show k + 15 * k = 16 * k by ring, pow_mul, zeta_pow_sixteen, one_pow]

/-- The key trigonometric identity: `ζ^k + ζ^(-k) = 2 cos (2πk/16)`. -/
