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

namespace Chem

open Polynomial Matrix

/-- The primitive 17-th root of unity `exp (2πi/17)`. -/

lemma A_mul_U : A * U = U * D := by
  ext j k
  rw [Matrix.mul_apply, sum_adj j (fun l => U l k), D, Matrix.mul_diagonal]
  have h1 : U (j - 1) k = zeta ^ (j.val * k.val) * (zeta ^ k.val)⁻¹ := by
    show zeta ^ ((j - 1).val * k.val) = _
    rw [zeta_pow_congr (Nat.ModEq.mul_right k.val (fin17_sub_one_val j)), add_mul, pow_add,
      zeta_pow_sixteen]
  have h2 : U (j + 1) k = zeta ^ (j.val * k.val) * zeta ^ k.val := by
    show zeta ^ ((j + 1).val * k.val) = _
    rw [zeta_pow_congr (Nat.ModEq.mul_right k.val (fin17_add_one_val j)), add_mul, pow_add,
      one_mul]
  rw [h1, h2, ← mul_add, add_comm (zeta ^ k.val)⁻¹, zeta_pow_add_inv k.val]
  rfl

