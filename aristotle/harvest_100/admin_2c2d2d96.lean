/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Finset

/-- The `n × n` quantum Fourier transform matrix:
`(QFT n) j k = n ^ (-1/2) * ω ^ (j * k)` where `ω = exp (2 π i / n)`. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => ((Real.sqrt n : ℝ) : ℂ)⁻¹ *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ ((j : ℕ) * (k : ℕ))

/-- The `n`-dimensional QFT matrix is unitary. -/
theorem qftMatrix_mem_unitaryGroup (n : ℕ) (hn : n ≠ 0) :
    qftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  obtain ⟨ω, hωdef, hp, hconj⟩ :
      ∃ ω : ℂ, qftMatrix n = (fun j k : Fin n =>
          ((Real.sqrt n : ℝ) : ℂ)⁻¹ * ω ^ ((j : ℕ) * (k : ℕ)))
        ∧ IsPrimitiveRoot ω n ∧ (starRingEnd ℂ) ω = ω⁻¹ := by
    refine ⟨Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n), rfl, ?_, ?_⟩
    · simpa [mul_div_assoc] using Complex.isPrimitiveRoot_exp n hn
    · rw [← Complex.exp_conj, ← Complex.exp_neg]
      congr 1
      rw [map_div₀]
      simp [Complex.ext_iff]
      ring
  have hω0 : ω ≠ 0 := hp.ne_zero hn
  have hsqrt : (((Real.sqrt n : ℝ) : ℂ))⁻¹ * (((Real.sqrt n : ℝ) : ℂ))⁻¹ = ((n : ℂ))⁻¹ := by
    have h1 : ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      simp
    rw [← mul_inv, h1]
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin n,
      qftMatrix n j k * (star (qftMatrix n)) k l
        = ((n : ℂ))⁻¹ * (ω ^ ((j : ℤ) - (l : ℤ))) ^ (k : ℕ) := by
    intro k
    rw [Matrix.star_apply]
    show _ * (starRingEnd ℂ) (qftMatrix n l k) = _
    rw [hωdef]
    simp only [map_mul, map_pow, map_inv₀, hconj, Complex.conj_ofReal]
    have hz : ω ^ ((j : ℕ) * (k : ℕ)) * (ω⁻¹) ^ ((l : ℕ) * (k : ℕ))
        = (ω ^ ((j : ℤ) - (l : ℤ))) ^ (k : ℕ) := by
      rw [inv_pow, ← zpow_natCast ω ((j : ℕ) * (k : ℕ)), ← zpow_natCast ω ((l : ℕ) * (k : ℕ)),
        ← zpow_neg, ← zpow_add₀ hω0, ← zpow_natCast (ω ^ ((j : ℤ) - (l : ℤ))) (k : ℕ),
        ← zpow_mul]
      congr 1
      push_cast
      ring
    calc ((Real.sqrt n : ℝ) : ℂ)⁻¹ * ω ^ ((j : ℕ) * (k : ℕ)) *
          (((Real.sqrt n : ℝ) : ℂ)⁻¹ * (ω⁻¹) ^ ((l : ℕ) * (k : ℕ)))
        = (((Real.sqrt n : ℝ) : ℂ)⁻¹ * ((Real.sqrt n : ℝ) : ℂ)⁻¹) *
            (ω ^ ((j : ℕ) * (k : ℕ)) * (ω⁻¹) ^ ((l : ℕ) * (k : ℕ))) := by ring
      _ = ((n : ℂ))⁻¹ * (ω ^ ((j : ℤ) - (l : ℤ))) ^ (k : ℕ) := by rw [hsqrt, hz]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun k => (ω ^ ((j : ℤ) - (l : ℤ))) ^ k) n]
  by_cases hjl : j = l
  · subst hjl
    have hzero : ((j : ℤ) - (j : ℤ)) = 0 := by ring
    rw [hzero]
    simp only [zpow_zero, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ (by exact_mod_cast hn)]
    simp
  · have hne : (ω ^ ((j : ℤ) - (l : ℤ))) ≠ 1 := by
      intro hcontra
      have hdvd := (hp.zpow_eq_one_iff_dvd _).mp hcontra
      have h1 : ((j : ℤ) - (l : ℤ)) ≠ 0 := by
        simp only [sub_ne_zero]
        exact_mod_cast fun h => hjl (Fin.ext (by exact_mod_cast h))
      have h2 : |(j : ℤ) - (l : ℤ)| < (n : ℤ) := by
        have hj := j.isLt
        have hl := l.isLt
        rw [abs_lt]
        constructor <;> omega
      have := Int.le_of_dvd (abs_pos.mpr h1) ((dvd_abs _ _).mpr hdvd)
      omega
    rw [geom_sum_eq hne]
    have hpow : (ω ^ ((j : ℤ) - (l : ℤ))) ^ n = 1 := by
      rw [← zpow_natCast (ω ^ ((j : ℤ) - (l : ℤ))) n, ← zpow_mul, mul_comm, zpow_mul]
      rw [zpow_natCast, hp.pow_eq_one, one_zpow]
    rw [hpow]
    simp [hjl]

/-- The 8-qubit (i.e. `2 ^ 8 = 256` dimensional) QFT matrix is unitary. -/
theorem qft_unitary_8 : qftMatrix (2 ^ 8) ∈ Matrix.unitaryGroup (Fin (2 ^ 8)) ℂ :=
  qftMatrix_mem_unitaryGroup _ (by norm_num)

end QC

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

