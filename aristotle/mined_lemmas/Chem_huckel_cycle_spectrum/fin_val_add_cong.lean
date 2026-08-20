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

lemma fin_val_add_cong {n : ℕ} (a b : Fin n) :
    (n : ℤ) ∣ (((a + b).val : ℤ) - ((a.val : ℤ) + b.val)) := by
  rw [Fin.val_add]
  have h := nat_mod_cong n (a.val + b.val)
  push_cast at h ⊢
  exact h

