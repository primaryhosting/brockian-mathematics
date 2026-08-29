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

import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix Finset

/-- The `N × N` discrete Fourier transform matrix, with entries
`(1/√N) · exp(2πi·jk/N)`. -/
noncomputable def dftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / N) / Real.sqrt N

/-- The quantum Fourier transform on `n` qubits: the `2ⁿ × 2ⁿ` DFT matrix. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := dftMatrix (2 ^ n)

section

variable {N : ℕ}

/-- The primitive `N`-th root of unity `exp(2πi/N)`. -/
private noncomputable def zeta (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

private lemma zeta_ne_zero : zeta N ≠ 0 := Complex.exp_ne_zero _

private lemma isPrimitiveRoot_zeta (hN : N ≠ 0) : IsPrimitiveRoot (zeta N) N :=
  Complex.isPrimitiveRoot_exp N hN

private lemma conj_zeta : (starRingEnd ℂ) (zeta N) = (zeta N)⁻¹ := by
  rw [zeta, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.ext_iff, neg_div]

private lemma dftMatrix_apply (j k : Fin N) :
    dftMatrix N j k = (zeta N) ^ ((j : ℕ) * (k : ℕ)) / Real.sqrt N := by
  rw [dftMatrix, zeta, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- Geometric sum of a nontrivial power of a primitive root of unity vanishes. -/
private lemma sum_zpow_eq_zero (hN : N ≠ 0) (m : ℤ) (hm : ¬ ((N : ℤ) ∣ m)) :
    ∑ j : Fin N, ((zeta N) ^ m) ^ (j : ℕ) = 0 := by
  set w : ℂ := (zeta N) ^ m with hw
  have hne : w ≠ 1 := by
    rw [hw, ne_eq, (isPrimitiveRoot_zeta hN).zpow_eq_one_iff_dvd m]
    exact hm
  have hpow : w ^ N = 1 := by
    rw [hw, ← zpow_natCast ((zeta N) ^ m) N, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, (isPrimitiveRoot_zeta hN).pow_eq_one, _root_.one_zpow]
  rw [Fin.sum_univ_eq_sum_range (fun i => w ^ i) N, geom_sum_eq hne, hpow, sub_self, zero_div]

private lemma sqrt_mul_sqrt (N : ℕ) :
    ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  simp

/-- The DFT matrix is unitary. -/
theorem dftMatrix_unitary (hN : N ≠ 0) : dftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  rw [Matrix.mul_apply]
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have key : ∀ j : Fin N,
      (star (dftMatrix N) a j) * dftMatrix N j b
        = ((zeta N) ^ ((b : ℤ) - (a : ℤ))) ^ (j : ℕ) / (N : ℂ) := by
    intro j
    rw [Matrix.star_apply, dftMatrix_apply, dftMatrix_apply]
    have hstar : star ((zeta N) ^ ((j : ℕ) * (a : ℕ)) / (Real.sqrt N : ℝ))
        = (zeta N) ^ (-(((j : ℕ) * (a : ℕ) : ℕ) : ℤ)) / (Real.sqrt N : ℝ) := by
      rw [show (star : ℂ → ℂ) = (starRingEnd ℂ) from rfl, map_div₀, map_pow, conj_zeta,
        Complex.conj_ofReal, _root_.zpow_neg, zpow_natCast, inv_pow]
    rw [hstar, div_mul_div_comm, sqrt_mul_sqrt]
    congr 1
    rw [← zpow_natCast (zeta N) ((j : ℕ) * (b : ℕ)), ← zpow_add₀ zeta_ne_zero,
      ← zpow_natCast ((zeta N) ^ ((b : ℤ) - (a : ℤ))) (j : ℕ), ← _root_.zpow_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.sum_div]
  by_cases hab : a = b
  · subst hab
    simp [hNC, Finset.card_univ]
  · have hdvd : ¬ ((N : ℤ) ∣ ((b : ℤ) - (a : ℤ))) := by
      intro h
      have hb := b.isLt
      have ha := a.isLt
      have habs : |(b : ℤ) - (a : ℤ)| < (N : ℤ) := by
        rw [abs_lt]
        omega
      have h0 : (b : ℤ) - (a : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd h habs
      have hab2 : (a : ℕ) = (b : ℕ) := by omega
      exact hab (Fin.ext hab2)
    rw [sum_zpow_eq_zero hN _ hdvd, zero_div, Matrix.one_apply_ne hab]

end

/-- **The `n`-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary (n : ℕ) : qft n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  dftMatrix_unitary (by positivity)

end QC

