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

namespace QC

open Complex Finset

/-- The `n`-qubit quantum Fourier transform matrix, of size `2 ^ n × 2 ^ n`:
`(QFT)_{j,k} = (1 / √(2^n)) * exp (2 π i j k / 2^n)`. -/

lemma qft_row_sum (n : ℕ) (j l : Fin (2 ^ n)) :
    ∑ k : Fin (2 ^ n),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) : ℂ) * ((k : ℕ) : ℂ) /
            ((2 ^ n : ℕ) : ℂ)) *
          (starRingEnd ℂ)
            (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((l : ℕ) : ℂ) * ((k : ℕ) : ℂ) /
              ((2 ^ n : ℕ) : ℂ)))
      = if j = l then ((2 ^ n : ℕ) : ℂ) else 0 := by
  have hN : 0 < 2 ^ n := Nat.two_pow_pos n
  have hNc : ((2 ^ n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr hN.ne'
  set d : ℤ := (j : ℤ) - (l : ℤ) with hd
  set ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / ((2 ^ n : ℕ) : ℂ)) with hζ
  have hterm : ∀ k : Fin (2 ^ n),
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) : ℂ) * ((k : ℕ) : ℂ) /
          ((2 ^ n : ℕ) : ℂ)) *
        (starRingEnd ℂ)
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((l : ℕ) : ℂ) * ((k : ℕ) : ℂ) /
            ((2 ^ n : ℕ) : ℂ)))
        = ζ ^ (k : ℕ) := by
    intro k
    have hB : (starRingEnd ℂ)
        (2 * (Real.pi : ℂ) * Complex.I * ((l : ℕ) : ℂ) * ((k : ℕ) : ℂ) / ((2 ^ n : ℕ) : ℂ))
        = -(2 * (Real.pi : ℂ) * Complex.I * ((l : ℕ) : ℂ) * ((k : ℕ) : ℂ) /
            ((2 ^ n : ℕ) : ℂ)) := by
      simp [map_div₀, Complex.conj_ofReal, map_ofNat, neg_div]
    rw [← Complex.exp_conj, hB, ← Complex.exp_add, hζ, ← Complex.exp_nat_mul]
    congr 1
    field_simp
    push_cast [hd]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Fin.sum_univ_eq_sum_range (fun k => ζ ^ k) (2 ^ n)]
  by_cases hjl : j = l
  · have hd0 : d = 0 := by simp [hd, hjl]
    have : ζ = 1 := by rw [hζ, hd0]; simp
    simp [this, hjl]
  · have hd0 : d ≠ 0 := by
      simp only [hd, sub_ne_zero]
      exact_mod_cast fun h => hjl (Fin.ext (by exact_mod_cast h))
    have hlt : |d| < ((2 ^ n : ℕ) : ℤ) := by
      have hj : (j : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast j.isLt
      have hl : (l : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast l.isLt
      have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg _
      have hl0 : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg _
      rw [abs_lt]
      constructor <;> simp only [hd] <;> omega
    have hne : ζ ≠ 1 := by
      intro hcon
      rw [hζ, exp_eq_one_iff_dvd hN d] at hcon
      exact hd0 (Int.eq_zero_of_abs_lt_dvd hcon hlt)
    rw [sum_pow_eq_zero (exp_pow_eq_one hN d) hne, if_neg hjl]

/-- The `n`-qubit quantum Fourier transform matrix is unitary. -/
