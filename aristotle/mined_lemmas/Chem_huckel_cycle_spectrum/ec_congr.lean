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

lemma ec_congr {n : ℕ} (hn : 0 < n) {a b : ℤ} (h : (n : ℤ) ∣ a - b) : ec n a = ec n b := by
  have : ec n (a - b) = 1 := (ec_eq_one_iff hn _).2 h
  calc ec n a = ec n ((a - b) + b) := by ring_nf
    _ = ec n (a - b) * ec n b := ec_add n _ _
    _ = ec n b := by rw [this, one_mul]

