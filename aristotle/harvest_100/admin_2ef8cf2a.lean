/-
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
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

/-- The `N × N` discrete Fourier transform (QFT) matrix:
`F j k = exp (2 π i j k / N) / √N`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j.val * k.val) / N) / Real.sqrt N

/-- The QFT matrix on `n` qubits, of size `2 ^ n`. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := qftMatrix (2 ^ n)

/-- Sum of a geometric series whose ratio is an `N`-th root of unity. -/
lemma sum_pow_root_of_unity {N : ℕ} {η : ℂ} (hη : η ^ N = 1) :
    ∑ m : Fin N, η ^ (m : ℕ) = if η = 1 then (N : ℂ) else 0 := by
  by_cases h : η = 1
  · simp [h]
  · rw [if_neg h, Fin.sum_univ_eq_sum_range (fun m => η ^ m) N, geom_sum_eq h, hη]
    simp

/-- The entries of the QFT matrix in terms of the primitive root `ζ = exp (2 π i / N)`. -/
lemma qftMatrix_apply (N : ℕ) (j k : Fin N) :
    qftMatrix N j k =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / N) ^ (j.val * k.val) / Real.sqrt N := by
  unfold qftMatrix
  rw [← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- The `N × N` QFT matrix is unitary (for `N ≠ 0`). -/
theorem qftMatrix_mem_unitaryGroup (N : ℕ) (hN : N ≠ 0) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  set ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / N) with hζdef
  have hprim : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN
  have hζN : ζ ^ N = 1 := hprim.pow_eq_one
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h] at hζN
    simp [hNpos.ne'] at hζN
  have hconj : (starRingEnd ℂ) ζ = ζ⁻¹ := by
    rw [hζdef, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp [map_div₀, Complex.conj_I, map_ofNat]
    ring
  -- square root facts
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  rw [Matrix.mem_unitaryGroup_iff]
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ m : Fin N,
      qftMatrix N j m * (star (qftMatrix N) m k)
        = (ζ ^ (j : ℕ) * (starRingEnd ℂ) (ζ ^ (k : ℕ))) ^ (m : ℕ) / (N : ℂ) := by
    intro m
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, qftMatrix_apply,
      qftMatrix_apply, Complex.star_def, map_div₀, Complex.conj_ofReal, div_mul_div_comm, hsq,
      mul_pow, map_pow, map_pow, ← pow_mul, ← pow_mul]
  simp only [hterm]
  rw [← Finset.sum_div]
  set η : ℂ := ζ ^ (j : ℕ) * (starRingEnd ℂ) (ζ ^ (k : ℕ)) with hηdef
  have hηN : η ^ N = 1 := by
    rw [hηdef, mul_pow, ← pow_mul, mul_comm (j : ℕ) N, pow_mul, hζN, ← map_pow, ← pow_mul,
      mul_comm (k : ℕ) N, pow_mul, hζN]
    simp
  have hηz : η = ζ ^ ((j : ℤ) - (k : ℤ)) := by
    rw [hηdef, map_pow, hconj, zpow_sub₀ hζ0, inv_pow, zpow_natCast, zpow_natCast, div_eq_mul_inv]
  have hη1 : η = 1 ↔ j = k := by
    constructor
    · intro h
      rw [hηz, hprim.zpow_eq_one_iff_dvd] at h
      have hj := j.isLt
      have hk := k.isLt
      have hlt : |((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)| < (N : ℤ) := by
        rw [abs_lt]; omega
      have : (j : ℕ) = (k : ℕ) := by
        have := Int.eq_zero_of_abs_lt_dvd h hlt
        omega
      exact Fin.ext this
    · intro h
      subst h
      rw [hηz]
      simp
  rw [sum_pow_root_of_unity hηN]
  by_cases h : j = k
  · rw [if_pos (hη1.mpr h), if_pos h]
    exact div_self (by exact_mod_cast hN)
  · rw [if_neg (fun hh => h (hη1.mp hh)), if_neg h]
    simp

/-- The 7-qubit QFT matrix is unitary. -/
theorem qft_unitary_7 : qft 7 ∈ Matrix.unitaryGroup (Fin (2 ^ 7)) ℂ :=
  qftMatrix_mem_unitaryGroup (2 ^ 7) (by norm_num)

end QC

