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

lemma ec_eq_one_iff {n : ℕ} (hn : 0 < n) (m : ℤ) : ec n m = 1 ↔ (n : ℤ) ∣ m := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [ec, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    field_simp at hk
    exact_mod_cast hk
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; field_simp⟩

