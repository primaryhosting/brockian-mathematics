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

/-
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Finset Matrix

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/
noncomputable def omegaN (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

lemma omegaN_ne_zero (N : ℕ) : omegaN N ≠ 0 := Complex.exp_ne_zero _

lemma isPrimitiveRoot_omegaN (N : ℕ) (hN : N ≠ 0) : IsPrimitiveRoot (omegaN N) N :=
  Complex.isPrimitiveRoot_exp N hN

lemma conj_omegaN (N : ℕ) : (starRingEnd ℂ) (omegaN N) = (omegaN N)⁻¹ := by
  rw [omegaN, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.ext_iff]
  ring

/-- The `N`-dimensional discrete Fourier transform matrix
`F j k = exp (2 π i j k / N) / sqrt N`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => omegaN N ^ ((j : ℕ) * (k : ℕ)) / Real.sqrt N

/-- The `n`-qubit quantum Fourier transform matrix, acting on the `2 ^ n` basis states. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := qftMatrix (2 ^ n)

/-- Geometric sum of powers of a root of unity: it is `N` when the exponent shift is a
multiple of `N`, and `0` otherwise. -/
lemma sum_omegaN_zpow (N : ℕ) (hN : N ≠ 0) (d : ℤ) :
    ∑ m ∈ Finset.range N, (omegaN N ^ d) ^ m = if (N : ℤ) ∣ d then (N : ℂ) else 0 := by
  have hprim := isPrimitiveRoot_omegaN N hN
  have hpow : (omegaN N ^ d) ^ N = 1 := by
    rw [← zpow_natCast (omegaN N ^ d) N, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, IsPrimitiveRoot.pow_eq_one hprim, _root_.one_zpow]
  by_cases hd : (N : ℤ) ∣ d
  · have hz : omegaN N ^ d = 1 := (hprim.zpow_eq_one_iff_dvd d).mpr hd
    simp [hz, hd]
  · have hz : omegaN N ^ d ≠ 1 := fun h => hd ((hprim.zpow_eq_one_iff_dvd d).mp h)
    rw [geom_sum_eq hz, hpow, if_neg hd]
    simp

/-- The `N`-dimensional discrete Fourier transform matrix is unitary. -/
theorem qftMatrix_unitary (N : ℕ) (hN : N ≠ 0) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hsqrt : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hNpos.le]
    norm_cast
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [Matrix.mem_unitaryGroup_iff]
  ext j k
  rw [Matrix.mul_apply]
  have hconj : ∀ m : Fin N, qftMatrix N j m * (star (qftMatrix N) : Matrix (Fin N) (Fin N) ℂ) m k
      = (omegaN N ^ ((j : ℤ) - (k : ℤ))) ^ (m : ℕ) / (N : ℂ) := by
    intro m
    have hstar : (star (qftMatrix N) : Matrix (Fin N) (Fin N) ℂ) m k
        = (starRingEnd ℂ) (omegaN N ^ ((k : ℕ) * (m : ℕ))) / (Real.sqrt N : ℂ) := by
      simp [Matrix.star_apply, qftMatrix, Complex.conj_ofReal]
    rw [hstar, qftMatrix, map_pow, conj_omegaN, div_mul_div_comm, hsqrt]
    congr 1
    rw [← zpow_natCast (omegaN N ^ ((j : ℤ) - (k : ℤ))) (m : ℕ), ← _root_.zpow_mul,
      ← zpow_natCast (omegaN N) ((j : ℕ) * (m : ℕ)),
      ← zpow_natCast ((omegaN N)⁻¹) ((k : ℕ) * (m : ℕ)),
      _root_.inv_zpow, ← _root_.zpow_neg, ← zpow_add₀ (omegaN_ne_zero N)]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun m _ => hconj m), ← Finset.sum_div]
  have hrange : ∑ m : Fin N, (omegaN N ^ ((j : ℤ) - (k : ℤ))) ^ (m : ℕ)
      = ∑ m ∈ Finset.range N, (omegaN N ^ ((j : ℤ) - (k : ℤ))) ^ m :=
    (Finset.sum_range fun m => (omegaN N ^ ((j : ℤ) - (k : ℤ))) ^ m).symm
  rw [hrange, sum_omegaN_zpow N hN]
  have hiff : ((N : ℤ) ∣ ((j : ℤ) - (k : ℤ))) ↔ j = k := by
    constructor
    · intro h
      have hlt : |(j : ℤ) - (k : ℤ)| < (N : ℤ) := by
        have hj := j.isLt
        have hk := k.isLt
        rw [abs_lt]
        constructor <;> omega
      have h0 := Int.eq_zero_of_abs_lt_dvd h hlt
      exact Fin.ext (by omega)
    · rintro rfl
      simp
  by_cases h : j = k
  · rw [if_pos (hiff.mpr h), div_self hNC, h, Matrix.one_apply_eq]
  · rw [if_neg (fun hd => h (hiff.mp hd)), Matrix.one_apply_ne h, zero_div]

/-- The `n`-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary (n : ℕ) : qft n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  qftMatrix_unitary (2 ^ n) (by positivity)

end QC

