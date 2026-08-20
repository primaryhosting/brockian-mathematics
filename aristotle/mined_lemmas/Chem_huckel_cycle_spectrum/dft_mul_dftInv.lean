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

lemma dft_mul_dftInv {n : ℕ} (hn : 0 < n) : dftMatrix n * dftInv n = 1 := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  ext i k
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin n, dftMatrix n i j * dftInv n j k
      = (n : ℂ)⁻¹ * ec n (((i.val : ℤ) - k.val) * j.val) := by
    intro j
    simp only [dftMatrix, dftInv]
    rw [show (((i.val : ℤ) - k.val) * j.val)
        = ((i.val : ℤ) * j.val) + (-((j.val : ℤ) * k.val)) by ring, ec_add]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, sum_ec_eq hn]
  rw [Matrix.one_apply]
  by_cases h : i = k
  · rw [if_pos h, if_pos h]; field_simp
  · rw [if_neg h, if_neg h]; ring

