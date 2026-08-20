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
