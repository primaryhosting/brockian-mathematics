/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real

namespace QC

open Complex Matrix Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The `n × n` quantum Fourier transform matrix,
`Q j k = (1/√n) · exp (2πi·j·k/n)`. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k =>
    ((1 / Real.sqrt n : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / n)

lemma zeta_pow (n : ℕ) (m : ℕ) :
    zeta n ^ m = Complex.exp (2 * Real.pi * Complex.I * m / n) := by
  rw [zeta, ← Complex.exp_nat_mul]
  ring_nf

lemma qftMatrix_apply (n : ℕ) (j k : Fin n) :
    qftMatrix n j k = ((1 / Real.sqrt n : ℝ) : ℂ) * zeta n ^ ((j : ℕ) * (k : ℕ)) := by
  rw [qftMatrix, zeta_pow]
  push_cast
  rfl

lemma zeta_isPrimitiveRoot (n : ℕ) (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n := by
  simpa [zeta, mul_assoc, mul_comm, mul_left_comm] using Complex.isPrimitiveRoot_exp n hn

lemma abs_zeta (n : ℕ) : ‖zeta n‖ = 1 := by
  rw [zeta, Complex.norm_exp]
  simp [Complex.div_re, Complex.mul_re]

lemma conj_zeta_pow (n m : ℕ) :
    (starRingEnd ℂ) (zeta n ^ m) = (zeta n ^ m)⁻¹ := by
  rw [← Complex.inv_eq_conj]
  rw [norm_pow, abs_zeta, one_pow]

/-- Geometric sum of an `n`-th root of unity different from `1` vanishes. -/
lemma sum_pow_eq_zero {x : ℂ} {n : ℕ} (hxn : x ^ n = 1) (hx : x ≠ 1) :
    ∑ j : Fin n, x ^ (j : ℕ) = 0 := by
  have h : (∑ i ∈ Finset.range n, x ^ i) * (x - 1) = x ^ n - 1 := geom_sum_mul x n
  rw [hxn, sub_self] at h
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have : ∑ i ∈ Finset.range n, x ^ i = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' hx1
  rw [Fin.sum_univ_eq_sum_range (fun i => x ^ i) n]
  exact this

/-- Orthogonality of the rows of the QFT matrix. -/
lemma qft_row_orthogonality (n : ℕ) (hn : n ≠ 0) (k l : Fin n) :
    ∑ j : Fin n, zeta n ^ ((k : ℕ) * (j : ℕ)) * (zeta n ^ ((l : ℕ) * (j : ℕ)))⁻¹
      = if k = l then (n : ℂ) else 0 := by
  have hz : IsPrimitiveRoot (zeta n) n := zeta_isPrimitiveRoot n hn
  have hzne : zeta n ≠ 0 := by
    intro h
    have := abs_zeta n
    rw [h] at this
    simp at this
  set x : ℂ := zeta n ^ ((k : ℤ) - (l : ℤ)) with hxdef
  have hterm : ∀ j : Fin n,
      zeta n ^ ((k : ℕ) * (j : ℕ)) * (zeta n ^ ((l : ℕ) * (j : ℕ)))⁻¹ = x ^ (j : ℕ) := by
    intro j
    rw [hxdef, ← zpow_natCast (zeta n) ((k : ℕ) * (j : ℕ)),
      ← zpow_natCast (zeta n) ((l : ℕ) * (j : ℕ)), ← _root_.zpow_neg, ← zpow_add₀ hzne,
      ← zpow_natCast (zeta n ^ ((k : ℤ) - (l : ℤ))) (j : ℕ), ← _root_.zpow_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  by_cases hkl : k = l
  · subst hkl
    simp [hxdef]
  · rw [if_neg hkl]
    apply sum_pow_eq_zero
    · rw [hxdef, ← zpow_natCast (zeta n ^ ((k : ℤ) - (l : ℤ))) n, ← _root_.zpow_mul, mul_comm,
        _root_.zpow_mul, hz.zpow_eq_one, _root_.one_zpow]
    · rw [hxdef]
      intro h
      rw [hz.zpow_eq_one_iff_dvd] at h
      have hk : (k : ℕ) < n := k.isLt
      have hl : (l : ℕ) < n := l.isLt
      have habs : |((k : ℤ) - (l : ℤ))| < (n : ℤ) := by
        rw [abs_lt]
        omega
      have hzero : ((k : ℤ) - (l : ℤ)) = 0 := Int.eq_zero_of_abs_lt_dvd h habs
      have hkln : (k : ℕ) = (l : ℕ) := by omega
      exact hkl (Fin.ext hkln)

/-- The `n × n` QFT matrix is unitary. -/
theorem qft_unitary (n : ℕ) (hn : n ≠ 0) : qftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext k l
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, qftMatrix_apply, Matrix.one_apply]
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc : ((1 / Real.sqrt n : ℝ) : ℂ) * ((1 / Real.sqrt n : ℝ) : ℂ) = ((n : ℂ))⁻¹ := by
    rw [← Complex.ofReal_mul]
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hnR]
    push_cast
    ring
  have hstep : ∀ x : Fin n,
      ((1 / Real.sqrt n : ℝ) : ℂ) * zeta n ^ ((k : ℕ) * (x : ℕ)) *
          star (((1 / Real.sqrt n : ℝ) : ℂ) * zeta n ^ ((l : ℕ) * (x : ℕ)))
        = (((1 / Real.sqrt n : ℝ) : ℂ) * ((1 / Real.sqrt n : ℝ) : ℂ)) *
            (zeta n ^ ((k : ℕ) * (x : ℕ)) * (zeta n ^ ((l : ℕ) * (x : ℕ)))⁻¹) := by
    intro x
    rw [star_mul']
    rw [show star (((1 / Real.sqrt n : ℝ) : ℂ)) = ((1 / Real.sqrt n : ℝ) : ℂ) from
      Complex.conj_ofReal _]
    rw [show star (zeta n ^ ((l : ℕ) * (x : ℕ))) = (zeta n ^ ((l : ℕ) * (x : ℕ)))⁻¹ from
      conj_zeta_pow n _]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hstep x), ← Finset.mul_sum, hc,
    qft_row_orthogonality n hn k l]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  by_cases hkl : k = l
  · simp [hkl, inv_mul_cancel₀ hn']
  · simp [hkl]

/-- The 6-qubit QFT matrix (of size `2^6 = 64`) is unitary. -/
theorem qft_unitary_6 : qftMatrix (2 ^ 6) ∈ Matrix.unitaryGroup (Fin (2 ^ 6)) ℂ :=
  qft_unitary (2 ^ 6) (by norm_num)

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

