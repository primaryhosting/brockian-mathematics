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

namespace QC

/-- The primitive `128`-th root of unity `exp (2 π i / 128)` used by the 7-qubit QFT. -/

theorem qft_unitary_7 : qft7 ∈ Matrix.unitaryGroup (Fin 128) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hs : (0:ℝ) ≤ 128 := by norm_num
  have hsq : (Real.sqrt 128 : ℝ) ^ 2 = 128 := Real.sq_sqrt hs
  have hsne : (Real.sqrt 128 : ℝ) ≠ 0 := by
    have : (0:ℝ) < Real.sqrt 128 := Real.sqrt_pos.2 (by norm_num)
    exact ne_of_gt this
  have hsC : ((Real.sqrt 128 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsne
  ext j k
  rw [Matrix.mul_apply]
  have hterm : ∀ l : Fin 128,
      qft7 j l * (star qft7) l k
        = (((Real.sqrt 128 : ℝ) : ℂ) ^ 2)⁻¹ *
            (omega7 ^ ((j : ℤ) - (k : ℤ))) ^ (l : ℕ) := by
    intro l
    have hstar : (star qft7) l k = (starRingEnd ℂ) (qft7 k l) := rfl
    rw [hstar]
    simp only [qft7, Matrix.of_apply, map_div₀, Complex.conj_ofReal, conj_omega7_pow]
    have hj : omega7 ^ ((j : ℕ) * (l : ℕ)) = (omega7 ^ (j : ℤ)) ^ (l : ℕ) := by
      rw [← zpow_natCast omega7 ((j:ℕ) * (l:ℕ)), ← zpow_natCast (omega7 ^ (j:ℤ)) (l:ℕ),
        ← zpow_mul]
      norm_cast
    have hk : (omega7 ^ ((k : ℕ) * (l : ℕ)))⁻¹ = (omega7 ^ (-(k : ℤ))) ^ (l : ℕ) := by
      rw [← zpow_natCast omega7 ((k:ℕ) * (l:ℕ)), ← zpow_neg,
        ← zpow_natCast (omega7 ^ (-(k:ℤ))) (l:ℕ), ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [hj, hk]
    have hsplit : (omega7 ^ ((j : ℤ) - (k : ℤ))) ^ (l : ℕ)
        = (omega7 ^ (j : ℤ)) ^ (l : ℕ) * (omega7 ^ (-(k : ℤ))) ^ (l : ℕ) := by
      rw [← mul_pow, ← zpow_add₀ omega7_ne_zero]
      ring_nf
    rw [hsplit]
    field_simp
  rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.mul_sum]
  have hsum : ∑ l : Fin 128, (omega7 ^ ((j : ℤ) - (k : ℤ))) ^ (l : ℕ)
      = ∑ l ∈ Finset.range 128, (omega7 ^ ((j : ℤ) - (k : ℤ))) ^ l := by
    rw [Finset.sum_range fun l => (omega7 ^ ((j : ℤ) - (k : ℤ))) ^ l]
  rw [hsum, geom_sum_omega7]
  have hdvd : ((128 : ℤ) ∣ ((j : ℤ) - (k : ℤ))) ↔ j = k := by
    constructor
    · intro h
      have hj : (j : ℕ) < 128 := j.isLt
      have hk : (k : ℕ) < 128 := k.isLt
      have : (j : ℤ) = (k : ℤ) := by omega
      have : (j : ℕ) = (k : ℕ) := by exact_mod_cast this
      exact Fin.ext this
    · intro h; simp [h]
  have hcast : (((Real.sqrt 128 : ℝ) : ℂ) ^ 2) = (128 : ℂ) := by
    rw [← Complex.ofReal_pow, hsq]
    norm_cast
  by_cases h : j = k
  · subst h
    rw [if_pos (hdvd.2 rfl), hcast, Matrix.one_apply_eq]
    exact inv_mul_cancel₀ (by norm_num)
  · rw [if_neg (fun hd => h (hdvd.1 hd)), Matrix.one_apply_ne h, mul_zero]

/-- Explicit form of unitarity: `qft7 * qft7ᴴ = 1`. -/
