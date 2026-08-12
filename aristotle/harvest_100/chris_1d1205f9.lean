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
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun j k =>
    (Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ)⁻¹ *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) : ℂ) * ((k : ℕ) : ℂ) /
        ((2 ^ n : ℕ) : ℂ))

/-- If `ζ` is an `N`-th root of unity different from `1`, the sum of its powers vanishes. -/
lemma sum_pow_eq_zero {ζ : ℂ} {N : ℕ} (hN : ζ ^ N = 1) (hne : ζ ≠ 1) :
    ∑ k ∈ Finset.range N, ζ ^ k = 0 := by
  rw [geom_sum_eq hne, hN, sub_self, zero_div]

/-- The root of unity `exp (2 π i d / N)` equals `1` only when `N ∣ d`. -/
lemma exp_eq_one_iff_dvd {N : ℕ} (hN : 0 < N) (d : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (d : ℂ) / (N : ℂ)) = 1 ↔ (N : ℤ) ∣ d := by
  have hNc : (N : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr hN.ne'
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    field_simp at hm
    exact_mod_cast hm
  · rintro ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    push_cast
    field_simp

/-- `exp (2 π i d / N)` is an `N`-th root of unity. -/
lemma exp_pow_eq_one {N : ℕ} (hN : 0 < N) (d : ℤ) :
    (Complex.exp (2 * Real.pi * Complex.I * (d : ℂ) / (N : ℂ))) ^ N = 1 := by
  have hNc : (N : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr hN.ne'
  rw [← Complex.exp_nat_mul]
  have : (N : ℂ) * (2 * Real.pi * Complex.I * (d : ℂ) / (N : ℂ))
      = (d : ℂ) * (2 * Real.pi * Complex.I) := by
    field_simp
  rw [this, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

/-- Orthogonality of the QFT rows: the key exponential-sum identity. -/
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
theorem qft_unitary (n : ℕ) : qft n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  have hN : 0 < 2 ^ n := Nat.two_pow_pos n
  have hNR : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by positivity
  have hsq : ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ))⁻¹ * ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ))⁻¹
      = (((2 ^ n : ℕ) : ℂ))⁻¹ := by
    rw [← mul_inv]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hNR]
    push_cast
    ring
  have hNc : ((2 ^ n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr hN.ne'
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hstep : ∀ k : Fin (2 ^ n), qft n j k * (star (qft n)) k l
      = ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ))⁻¹ * ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ))⁻¹ *
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) : ℂ) * ((k : ℕ) : ℂ) /
            ((2 ^ n : ℕ) : ℂ)) *
          (starRingEnd ℂ)
            (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((l : ℕ) : ℂ) * ((k : ℕ) : ℂ) /
              ((2 ^ n : ℕ) : ℂ)))) := by
    intro k
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, qft, map_mul,
      Complex.conj_ofReal, map_inv₀, Complex.star_def, map_mul]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hstep k), ← Finset.mul_sum, qft_row_sum n j l, hsq]
  by_cases hjl : j = l
  · rw [if_pos hjl, if_pos hjl, inv_mul_cancel₀ hNc]
  · rw [if_neg hjl, if_neg hjl, mul_zero]

end QC

