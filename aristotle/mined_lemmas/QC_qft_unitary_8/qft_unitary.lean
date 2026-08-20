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

open Complex

/-- The primitive `n`-th root of unity `exp (2πi / n)` used by the discrete Fourier transform. -/

theorem qft_unitary (n : ℕ) (hn : n ≠ 0) : qftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hsqrt : ((Real.sqrt n : ℝ) : ℂ)⁻¹ * ((Real.sqrt n : ℝ) : ℂ)⁻¹ = ((n : ℂ))⁻¹ := by
    have h : ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hnpos.le]
      simp
    rw [← mul_inv, h]
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ i : Fin n, (star (qftMatrix n)) j i * qftMatrix n i k
      = ((n : ℂ))⁻¹ * (omega n ^ ((k : ℤ) - (j : ℤ))) ^ (i : ℕ) := by
    intro i
    rw [Matrix.star_apply]
    show (starRingEnd ℂ) (qftMatrix n i j) * qftMatrix n i k = _
    rw [qftMatrix, qftMatrix]
    simp only [map_mul, map_pow, conj_omega, map_inv₀, Complex.conj_ofReal]
    rw [show ((Real.sqrt n : ℝ) : ℂ)⁻¹ * (omega n)⁻¹ ^ ((i : ℕ) * (j : ℕ)) *
        (((Real.sqrt n : ℝ) : ℂ)⁻¹ * omega n ^ ((i : ℕ) * (k : ℕ)))
        = (((Real.sqrt n : ℝ) : ℂ)⁻¹ * ((Real.sqrt n : ℝ) : ℂ)⁻¹) *
          ((omega n)⁻¹ ^ ((i : ℕ) * (j : ℕ)) * omega n ^ ((i : ℕ) * (k : ℕ))) by ring]
    rw [hsqrt]
    congr 1
    exact omega_inv_pow_mul n (i : ℕ) (j : ℕ) (k : ℕ)
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun i => (omega n ^ ((k : ℤ) - (j : ℤ))) ^ i) n]
  by_cases h : j = k
  · subst h
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [sub_self, zpow_zero, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, if_true]
    field_simp
  · have hd : ¬ ((n : ℤ) ∣ ((k : ℤ) - (j : ℤ))) := by
      intro hdvd
      have hjk : (j : ℕ) < n := j.isLt
      have hkn : (k : ℕ) < n := k.isLt
      have habs : |(k : ℤ) - (j : ℤ)| < (n : ℤ) := by
        rw [abs_lt]; omega
      have := Int.eq_zero_of_abs_lt_dvd hdvd habs
      exact h (Fin.ext (by omega))
    rw [sum_omega_zpow_eq_zero n hn _ hd, mul_zero, if_neg h]

/-- The 8-qubit quantum Fourier transform matrix (dimension `2^8 = 256`) is unitary. -/
