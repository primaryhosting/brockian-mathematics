/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/
noncomputable def zeta (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / N)

/-- The `N × N` quantum Fourier transform matrix:
`(QFT_N)_{j,k} = (1/√N) · exp (2πi·j·k/N)`.
For `N = 2^n` this is the QFT acting on `n` qubits. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => (1 / Real.sqrt N : ℝ) * Complex.exp (2 * Real.pi * I * (j * k) / N)

lemma qftMatrix_apply (N : ℕ) (j k : Fin N) :
    qftMatrix N j k = (1 / Real.sqrt N : ℝ) * zeta N ^ ((j : ℕ) * (k : ℕ)) := by
  have h : (2 * (Real.pi : ℂ) * I * ((j : ℕ) * (k : ℕ)) / N)
      = ((j : ℕ) * (k : ℕ) : ℕ) * (2 * (Real.pi : ℂ) * I / N) := by
    push_cast; ring
  simp only [qftMatrix, zeta, h, Complex.exp_nat_mul]

lemma zeta_ne_zero (N : ℕ) : zeta N ≠ 0 := Complex.exp_ne_zero _

lemma conj_zeta (N : ℕ) : (starRingEnd ℂ) (zeta N) = (zeta N)⁻¹ := by
  rw [zeta, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.ext_iff]
  ring

lemma isPrimitiveRoot_zeta (N : ℕ) (hN : N ≠ 0) : IsPrimitiveRoot (zeta N) N :=
  Complex.isPrimitiveRoot_exp N hN

lemma zeta_zpow_ne_one (N : ℕ) (hN : N ≠ 0) {j l : Fin N} (h : j ≠ l) :
    zeta N ^ ((l : ℤ) - (j : ℤ)) ≠ 1 := by
  intro hone
  have hdvd : ((N : ℤ)) ∣ ((l : ℤ) - (j : ℤ)) :=
    ((isPrimitiveRoot_zeta N hN).zpow_eq_one_iff_dvd _).mp hone
  have hjl : (j : ℕ) ≠ (l : ℕ) := fun hh => h (Fin.ext hh)
  have h1 : ((l : ℤ) - (j : ℤ)) ≠ 0 := by
    have : ((j : ℕ) : ℤ) ≠ ((l : ℕ) : ℤ) := by exact_mod_cast hjl
    omega
  have h2 : |(l : ℤ) - (j : ℤ)| < (N : ℤ) := by
    have hj : (j : ℕ) < N := j.isLt
    have hl : (l : ℕ) < N := l.isLt
    have hj' : ((j : ℕ) : ℤ) < (N : ℤ) := by exact_mod_cast hj
    have hl' : ((l : ℕ) : ℤ) < (N : ℤ) := by exact_mod_cast hl
    have hj0 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := Int.natCast_nonneg _
    have hl0 : (0 : ℤ) ≤ ((l : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [abs_lt]
    omega
  have := Int.le_of_dvd (abs_pos.mpr h1) ((dvd_abs _ _).mpr hdvd)
  omega

lemma zeta_zpow_pow_card (N : ℕ) (hN : N ≠ 0) (j l : Fin N) :
    (zeta N ^ ((l : ℤ) - (j : ℤ))) ^ N = 1 := by
  rw [← zpow_natCast (zeta N ^ ((l : ℤ) - (j : ℤ))) N, ← _root_.zpow_mul, mul_comm,
    _root_.zpow_mul, zpow_natCast, (isPrimitiveRoot_zeta N hN).pow_eq_one, _root_.one_zpow]

/-- Orthogonality of the columns of the DFT matrix: the geometric sum of the powers of
`ζ^(l-j)` is `N` when `j = l` and `0` otherwise. -/
lemma sum_zeta_zpow (N : ℕ) (hN : N ≠ 0) (j l : Fin N) :
    ∑ k : Fin N, (zeta N ^ ((l : ℤ) - (j : ℤ))) ^ (k : ℕ)
      = if j = l then (N : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (zeta N ^ ((l : ℤ) - (j : ℤ))) ^ k) N]
  by_cases h : j = l
  · subst h
    simp
  · rw [geom_sum_eq (zeta_zpow_ne_one N hN h), zeta_zpow_pow_card N hN j l, if_neg h]
    simp

lemma qftMatrix_mem_unitaryGroup (N : ℕ) (hN : N ≠ 0) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j l
  rw [Matrix.mul_apply]
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := Nat.pos_of_ne_zero hN
    exact_mod_cast this
  have hprod : ((1 / Real.sqrt N : ℝ) : ℂ) * ((1 / Real.sqrt N : ℝ) : ℂ)
      = ((1 / (N : ℝ) : ℝ) : ℂ) := by
    norm_cast
    rw [div_mul_div_comm, Real.mul_self_sqrt hNpos.le]
    norm_num
  have hterm : ∀ k : Fin N,
      (star (qftMatrix N)) j k * qftMatrix N k l
        = ((1 / (N : ℝ) : ℝ) : ℂ) * (zeta N ^ ((l : ℤ) - (j : ℤ))) ^ (k : ℕ) := by
    intro k
    have hstar : (star (qftMatrix N)) j k = (starRingEnd ℂ) (qftMatrix N k j) := rfl
    rw [hstar, qftMatrix_apply, qftMatrix_apply]
    have hc : (starRingEnd ℂ) ((1 / Real.sqrt N : ℝ) * zeta N ^ ((k : ℕ) * (j : ℕ)))
        = ((1 / Real.sqrt N : ℝ) : ℂ) * (zeta N)⁻¹ ^ ((k : ℕ) * (j : ℕ)) := by
      simp [map_mul, map_pow, conj_zeta]
    have hz : (zeta N)⁻¹ ^ ((k : ℕ) * (j : ℕ)) * zeta N ^ ((k : ℕ) * (l : ℕ))
        = (zeta N ^ ((l : ℤ) - (j : ℤ))) ^ (k : ℕ) := by
      rw [← zpow_natCast (zeta N) ((k : ℕ) * (l : ℕ)), ← zpow_neg_one (zeta N),
        ← zpow_natCast ((zeta N) ^ (-1 : ℤ)) ((k : ℕ) * (j : ℕ)), ← _root_.zpow_mul,
        ← zpow_natCast (zeta N ^ ((l : ℤ) - (j : ℤ))) (k : ℕ), ← _root_.zpow_mul,
        ← zpow_add₀ (zeta_ne_zero N)]
      congr 1
      push_cast
      ring
    rw [hc]
    calc ((1 / Real.sqrt N : ℝ) : ℂ) * (zeta N)⁻¹ ^ ((k : ℕ) * (j : ℕ))
          * (((1 / Real.sqrt N : ℝ) : ℂ) * zeta N ^ ((k : ℕ) * (l : ℕ)))
        = (((1 / Real.sqrt N : ℝ) : ℂ) * ((1 / Real.sqrt N : ℝ) : ℂ))
          * ((zeta N)⁻¹ ^ ((k : ℕ) * (j : ℕ)) * zeta N ^ ((k : ℕ) * (l : ℕ))) := by ring
      _ = ((1 / (N : ℝ) : ℝ) : ℂ) * (zeta N ^ ((l : ℤ) - (j : ℤ))) ^ (k : ℕ) := by
          rw [hz, hprod]
  have hNC : (N : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hN
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, sum_zeta_zpow N hN]
  by_cases h : j = l
  · subst h
    rw [if_pos rfl, Matrix.one_apply_eq]
    push_cast
    field_simp
  · rw [if_neg h, Matrix.one_apply_ne h, mul_zero]

/-- The 5-qubit quantum Fourier transform matrix (of size `2 ^ 5 = 32`) is unitary. -/
theorem qft_unitary_5 : qftMatrix (2 ^ 5) ∈ Matrix.unitaryGroup (Fin (2 ^ 5)) ℂ :=
  qftMatrix_mem_unitaryGroup (2 ^ 5) (by norm_num)

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

