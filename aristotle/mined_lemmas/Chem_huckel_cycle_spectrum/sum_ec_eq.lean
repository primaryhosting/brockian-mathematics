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

lemma sum_ec_eq {n : ℕ} (hn : 0 < n) (i k : Fin n) :
    ∑ j : Fin n, ec n (((i.val : ℤ) - k.val) * j.val) = if i = k then (n : ℂ) else 0 := by
  set d : ℤ := (i.val : ℤ) - k.val with hd
  have hterm : ∀ j : Fin n, ec n (d * j.val) = (ec n d) ^ j.val := fun j => ec_mul_nat n d j.val
  rw [Finset.sum_congr rfl (fun j _ => hterm j),
    Fin.sum_univ_eq_sum_range (fun m => (ec n d) ^ m) n]
  by_cases h : i = k
  · have : d = 0 := by simp [hd, h]
    simp [this, ec_zero, h]
  · have hdne : d ≠ 0 := by
      simp only [hd, sub_ne_zero]
      exact_mod_cast fun hc => h (Fin.ext (by exact_mod_cast hc))
    have hndvd : ¬ ((n : ℤ) ∣ d) := by
      intro hdvd
      exact hdne (Int.eq_zero_of_abs_lt_dvd hdvd (by
        have h1 : i.val < n := i.isLt
        have h2 : k.val < n := k.isLt
        rw [abs_lt]
        constructor <;> [skip; skip] <;> simp only [hd] <;> omega))
    have hz : ec n d ≠ 1 := fun hc => hndvd ((ec_eq_one_iff hn d).1 hc)
    have hzn : (ec n d) ^ n = 1 := by
      rw [← ec_mul_nat]
      exact (ec_eq_one_iff hn _).2 ⟨d, by ring⟩
    rw [geom_sum_eq hz, hzn, if_neg h]
    simp

/-! ### Arithmetic in `Fin n` -/

