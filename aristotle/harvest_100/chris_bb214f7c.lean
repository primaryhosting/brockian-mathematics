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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

/-- The `N × N` discrete Fourier transform (quantum Fourier transform) matrix:
its `(j, k)` entry is `exp (2 π i j k / N) / √N`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / N) / (Real.sqrt N : ℝ)

/-- The quantum Fourier transform on `n` qubits, i.e. the DFT matrix of size `2 ^ n`. -/
noncomputable def qftQubits (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  qftMatrix (2 ^ n)

/-- Each entry of `(qftMatrix N)ᴴ * qftMatrix N` is a scaled geometric sum. -/
lemma qftMatrix_conj_mul_entry (N : ℕ) (hN : 0 < N) (j l k : Fin N) :
    (starRingEnd ℂ) (qftMatrix N k j) * qftMatrix N k l
      = (Complex.exp (2 * Real.pi * Complex.I * ((l : ℕ) - (j : ℕ)) / N)) ^ (k : ℕ) / (N : ℂ) := by
  have hsq : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  simp only [qftMatrix, map_div₀, ← Complex.exp_conj, Complex.conj_ofReal]
  rw [div_mul_div_comm, hsq]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_nat_mul]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat, map_natCast]
  ring

/-- For distinct indices the relevant geometric sum of roots of unity vanishes. -/
lemma sum_root_of_unity_eq_zero (N : ℕ) (hN : 0 < N) (j l : Fin N) (hjl : j ≠ l) :
    ∑ k : Fin N, (Complex.exp (2 * Real.pi * Complex.I * ((l : ℕ) - (j : ℕ)) / N)) ^ (k : ℕ)
      = 0 := by
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((l : ℕ) - (j : ℕ)) / N) with hz
  have hzN : z ^ N = 1 := by
    rw [hz, ← Complex.exp_nat_mul]
    have h : (N : ℂ) * (2 * Real.pi * Complex.I * ((l : ℕ) - (j : ℕ)) / N)
        = (((l : ℤ) - (j : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    field_simp at hn
    have keyZ : (l : ℤ) - (j : ℤ) = N * n := by exact_mod_cast hn
    have hdvd : (N : ℤ) ∣ ((l : ℤ) - (j : ℤ)) := ⟨n, keyZ⟩
    have habs : |((l : ℤ) - (j : ℤ))| < (N : ℤ) := by
      have h1 : (l : ℤ) < N := by exact_mod_cast l.isLt
      have h2 : (j : ℤ) < N := by exact_mod_cast j.isLt
      have h3 : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg _
      have h4 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg _
      rw [abs_lt]; omega
    have hzero := Int.eq_zero_of_abs_lt_dvd hdvd habs
    exact hjl (Fin.ext (by omega)).symm
  rw [Fin.sum_univ_eq_sum_range (fun k => z ^ k), geom_sum_eq hz1, hzN, sub_self, zero_div]

/-- The DFT matrix satisfies `Qᴴ * Q = 1`. -/
lemma qftMatrix_conjTranspose_mul_self (N : ℕ) (hN : 0 < N) :
    (qftMatrix N)ᴴ * qftMatrix N = 1 := by
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  ext j l
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_congr rfl (fun k _ => qftMatrix_conj_mul_entry N hN j l k), ← Finset.sum_div]
  by_cases hjl : j = l
  · subst hjl
    have hz : (Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) - (j : ℕ)) / N)) = 1 := by
      simp
    simp only [hz, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    rw [div_self hNne, Matrix.one_apply_eq]
  · rw [sum_root_of_unity_eq_zero N hN j l hjl, zero_div, Matrix.one_apply_ne hjl]

/-- The `N × N` quantum Fourier transform matrix is unitary. -/
theorem qftMatrix_mem_unitaryGroup (N : ℕ) (hN : 0 < N) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have h1 : (qftMatrix N)ᴴ * qftMatrix N = 1 := qftMatrix_conjTranspose_mul_self N hN
  refine ⟨h1, ?_⟩
  exact mul_eq_one_comm.mpr h1

/-- **The 5-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary_5 : qftQubits 5 ∈ Matrix.unitaryGroup (Fin (2 ^ 5)) ℂ :=
  qftMatrix_mem_unitaryGroup (2 ^ 5) (by norm_num)

end QC

