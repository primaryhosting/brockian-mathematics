/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

/-- The `N × N` discrete Fourier transform (quantum Fourier transform) matrix, whose
`(j, k)` entry is `exp(2πi·jk/N) / √N`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ) : ℕ) / N) / Real.sqrt N

/-- Complex conjugation negates the phase `2πi·n/N`. -/
private lemma conj_phase (N n : ℕ) :
    (starRingEnd ℂ) (2 * Real.pi * Complex.I * (n : ℕ) / N)
      = -(2 * Real.pi * Complex.I * (n : ℕ) / N) := by
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
    Complex.conj_natCast]
  ring

/-- Orthogonality of characters: the sum of `exp(2πi·i·m/N)` over `i < N` is `N` when
`N ∣ m` and `0` otherwise. -/
theorem sum_exp (N : ℕ) (hN : 0 < N) (m : ℤ) :
    ∑ i ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * ((i : ℂ) * (m : ℂ)) / N)
      = if (N : ℤ) ∣ m then (N : ℂ) else 0 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / N) with hz
  have hterm : ∀ i : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * ((i : ℂ) * (m : ℂ)) / N) = z ^ i := by
    intro i
    rw [hz, ← Complex.exp_nat_mul]
    ring_nf
  simp only [hterm]
  have hzone : z = 1 ↔ (N : ℤ) ∣ m := by
    rw [hz, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      field_simp at hn
      exact_mod_cast hn
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      subst hc
      push_cast
      field_simp
  by_cases h : (N : ℤ) ∣ m
  · simp [h, hzone.mpr h]
  · rw [if_neg h]
    have hz1 : z ≠ 1 := fun hh => h (hzone.mp hh)
    rw [geom_sum_eq hz1, show z ^ N = 1 from by
      rw [hz, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]; exact ⟨m, by field_simp⟩]
    simp

/-- The `N × N` quantum Fourier transform matrix is unitary for every `N > 0`. -/
theorem qft_unitary (N : ℕ) (hN : 0 < N) : qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    norm_num
  rw [Matrix.mem_unitaryGroup_iff]
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hentry : ∀ i : Fin N,
      qftMatrix N j i * (star (qftMatrix N) : Matrix (Fin N) (Fin N) ℂ) i k
        = Complex.exp (2 * Real.pi * Complex.I * ((i : ℕ) * ((j : ℤ) - (k : ℤ) : ℤ)) / N) / N := by
    intro i
    show _ * (starRingEnd ℂ) (qftMatrix N k i) = _
    simp only [qftMatrix, Matrix.of_apply]
    rw [map_div₀, Complex.conj_ofReal, ← Complex.exp_conj, conj_phase,
      div_mul_div_comm, ← Complex.exp_add, hsq]
    congr 1
    push_cast
    ring_nf
  simp only [hentry]
  rw [← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => Complex.exp (2 * Real.pi * Complex.I * ((i : ℂ) * (((j : ℤ) - (k : ℤ) : ℤ) : ℂ)) / N))
    N, sum_exp N hN]
  by_cases hjk : j = k
  · subst hjk
    simp [hNc]
  · have hd : ¬ ((N : ℤ) ∣ ((j : ℤ) - (k : ℤ))) := by
      intro hdvd
      have hj := j.isLt
      have hk := k.isLt
      have hzero : (j : ℤ) - (k : ℤ) = 0 :=
        Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; omega)
      exact hjk (Fin.ext (by omega))
    simp [hd, hjk]

/-- The 8-qubit quantum Fourier transform matrix (of size `2^8 = 256`) is unitary. -/
theorem qft_unitary_8 : qftMatrix (2 ^ 8) ∈ Matrix.unitaryGroup (Fin (2 ^ 8)) ℂ :=
  qft_unitary (2 ^ 8) (by norm_num)

end QC

