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

lemma cycle_neighbors_ne {n : ℕ} [NeZero n] (hn : 3 ≤ n) (i : Fin n) : i - 1 ≠ i + 1 := by
  intro h
  have h1 : ((1 : Fin n) : ℕ) = 1 := fin_val_one (by omega)
  have hs := fin_val_sub_cong i 1
  have ha := fin_val_add_cong i 1
  have h1' : (((1 : Fin n) : ℕ) : ℤ) = 1 := by exact_mod_cast h1
  rw [h, h1'] at hs
  rw [h1'] at ha
  have h2 : (n : ℤ) ∣ 2 := by
    have hd := dvd_sub hs ha
    have : (((i + 1).val : ℤ) - ((i.val : ℤ) - 1)) - (((i + 1).val : ℤ) - ((i.val : ℤ) + 1))
        = 2 := by ring
    rwa [this] at hd
  have := Int.le_of_dvd (by norm_num) h2
  omega

/-! ### The eigenvector relation -/

/-- Shifting the row index of the DFT matrix multiplies the entry by a root of unity. -/
