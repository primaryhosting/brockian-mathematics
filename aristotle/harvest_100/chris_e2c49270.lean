/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The `N`-dimensional quantum Fourier transform matrix:
`(QFT_N)_{j,k} = exp(2πi·j·k/N) / √N`. -/
noncomputable def qft (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k =>
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * (k : ℕ) : ℕ) / (N : ℂ)) /
      (Real.sqrt N : ℂ)

/-- The root of unity `exp(2πi d / N)`. -/
noncomputable def zeta (N : ℕ) (d : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))

lemma zeta_pow (N : ℕ) (d : ℤ) (m : ℕ) :
    (zeta N d) ^ m = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * (d : ℂ)) / (N : ℂ)) := by
  rw [zeta, ← Complex.exp_nat_mul]
  congr 1
  ring

lemma zeta_pow_card (N : ℕ) (hN : 0 < N) (d : ℤ) : (zeta N d) ^ N = 1 := by
  rw [zeta_pow]
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have : 2 * (Real.pi : ℂ) * Complex.I * ((N : ℂ) * (d : ℂ)) / (N : ℂ)
      = (d : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    field_simp
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma zeta_ne_one (N : ℕ) (hN : 0 < N) (d : ℤ) (hd : ¬ ((N : ℤ) ∣ d)) : zeta N d ≠ 1 := by
  intro h
  rw [zeta, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hd' : (d : ℂ) = (n : ℂ) * (N : ℂ) := by
    field_simp at hn
    linear_combination hn
  have : d = n * (N : ℤ) := by exact_mod_cast hd'
  exact hd ⟨n, by rw [this]; ring⟩

/-- Geometric sum of a nontrivial `N`-th root of unity vanishes. -/
lemma sum_zeta_pow_eq_zero (N : ℕ) (hN : 0 < N) (d : ℤ) (hd : ¬ ((N : ℤ) ∣ d)) :
    ∑ m ∈ Finset.range N, (zeta N d) ^ m = 0 := by
  rw [geom_sum_eq (zeta_ne_one N hN d hd), zeta_pow_card N hN d]
  simp

lemma zeta_zero (N : ℕ) : zeta N 0 = 1 := by
  simp [zeta]

/-- The key entrywise identity: the product of the conjugated `(m,j)` entry with the `(m,k)`
entry is `ζ^m / N` for `ζ = exp(2πi(k-j)/N)`. -/
lemma conj_qft_mul_qft (N : ℕ) (hN : 0 < N) (m j k : Fin N) :
    (starRingEnd ℂ) (qft N m j) * qft N m k
      = (zeta N ((k : ℕ) - (j : ℕ) : ℤ)) ^ (m : ℕ) / (N : ℂ) := by
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    norm_num
  have hsqne : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hsq
    exact hNne hsq.symm
  have hconj : (starRingEnd ℂ) (qft N m j)
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (((m : ℕ) * (j : ℕ) : ℕ) : ℂ) / (N : ℂ))) /
        ((Real.sqrt N : ℝ) : ℂ) := by
    rw [qft, map_div₀, ← Complex.exp_conj]
    congr 2
    · simp [Complex.ext_iff]
      ring
    · simp
  rw [hconj, qft, zeta_pow, div_mul_div_comm, ← Complex.exp_add, hsq]
  congr 2
  push_cast
  field_simp
  ring

/-- The QFT matrix satisfies `Aᴴ * A = 1`. -/
theorem qft_conjTranspose_mul_self (N : ℕ) (hN : 0 < N) :
    (qft N).conjTranspose * qft N = 1 := by
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  ext j k
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Complex.star_def]
  have hterm : ∀ m : Fin N, (starRingEnd ℂ) (qft N m j) * qft N m k
      = (zeta N ((k : ℕ) - (j : ℕ) : ℤ)) ^ (m : ℕ) / (N : ℂ) :=
    fun m => conj_qft_mul_qft N hN m j k
  rw [Finset.sum_congr rfl (fun m _ => hterm m)]
  rw [← Finset.sum_div]
  have hsum : ∑ m : Fin N, (zeta N ((k : ℕ) - (j : ℕ) : ℤ)) ^ (m : ℕ)
      = ∑ m ∈ Finset.range N, (zeta N ((k : ℕ) - (j : ℕ) : ℤ)) ^ m := by
    rw [Finset.sum_range fun m => (zeta N ((k : ℕ) - (j : ℕ) : ℤ)) ^ m]
  rw [hsum]
  by_cases hjk : j = k
  · subst hjk
    have : ((j : ℕ) - (j : ℕ) : ℤ) = 0 := by ring
    rw [this, zeta_zero]
    simp [hNne]
  · have hd : ¬ ((N : ℤ) ∣ ((k : ℕ) - (j : ℕ) : ℤ)) := by
      intro hdvd
      have habs : |((k : ℕ) - (j : ℕ) : ℤ)| < (N : ℤ) := by
        have hk : (k : ℕ) < N := k.isLt
        have hjlt : (j : ℕ) < N := j.isLt
        rw [abs_lt]
        omega
      have := Int.eq_zero_of_abs_lt_dvd hdvd habs
      have : (k : ℕ) = (j : ℕ) := by omega
      exact hjk (Fin.ext this).symm
    rw [sum_zeta_pow_eq_zero N hN _ hd]
    simp [hjk]

/-- The 8-qubit QFT matrix (dimension `2^8 = 256`) is unitary. -/
theorem qft_unitary_8 : qft (2 ^ 8) ∈ Matrix.unitaryGroup (Fin (2 ^ 8)) ℂ := by
  have hN : 0 < 2 ^ 8 := by norm_num
  have h1 : (qft (2 ^ 8)).conjTranspose * qft (2 ^ 8) = 1 := qft_conjTranspose_mul_self _ hN
  have h2 : qft (2 ^ 8) * (qft (2 ^ 8)).conjTranspose = 1 := mul_eq_one_comm.mp h1
  exact ⟨h1, h2⟩

end QC

#print axioms QC.qft_unitary_8

