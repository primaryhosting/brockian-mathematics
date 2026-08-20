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

open Matrix

/-- `ec n m = exp (2 π i m / n)`, an `n`-th root of unity raised to the power `m`. -/

lemma ec_mul_nat (n : ℕ) (a : ℤ) (m : ℕ) : ec n (a * m) = (ec n a) ^ m := by
  induction m with
  | zero => simp [ec_zero]
  | succ m ih =>
      have : a * ((m : ℤ) + 1) = a * m + a := by ring
      push_cast
      rw [this, ec_add, ih, pow_succ]

/-- The two conjugate `n`-th roots of unity add up to twice a cosine. -/
