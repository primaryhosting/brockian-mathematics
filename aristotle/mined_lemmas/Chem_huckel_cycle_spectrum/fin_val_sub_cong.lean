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

lemma fin_val_sub_cong {n : ℕ} (a b : Fin n) :
    (n : ℤ) ∣ (((a - b).val : ℤ) - ((a.val : ℤ) - b.val)) := by
  rw [Fin.sub_def]
  have h := nat_mod_cong n (n - b.val + a.val)
  have hb : ((n - b.val + a.val : ℕ) : ℤ) = (n : ℤ) - b.val + a.val := by
    have hble : b.val ≤ n := b.isLt.le
    push_cast [Nat.cast_sub hble]; ring
  simp only []
  rw [hb] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c + 1, by push_cast at hc ⊢; linarith [hc]⟩

