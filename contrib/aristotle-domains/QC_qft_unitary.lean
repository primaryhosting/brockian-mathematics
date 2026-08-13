/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Statement: The n-qubit quantum Fourier transform matrix is unitary.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

open Complex

/-- The `N × N` discrete Fourier transform matrix:
`(dftMatrix N) j k = (1/√N) * exp (2πi jk / N)`. -/
noncomputable def dftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    (Real.sqrt N : ℂ)⁻¹ *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * (k : ℕ) : ℕ) / (N : ℂ))

/-- The `n`-qubit quantum Fourier transform matrix, of size `2^n × 2^n`. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  dftMatrix (2 ^ n)

/-- Primitive `N`-th root of unity used in the DFT. -/
noncomputable def zetaN (N : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

lemma isPrimitiveRoot_zetaN {N : ℕ} (hN : 0 < N) : IsPrimitiveRoot (zetaN N) N := by
  have := Complex.isPrimitiveRoot_exp N (by exact_mod_cast hN.ne')
  simpa [zetaN, mul_comm, mul_left_comm, mul_assoc] using this

lemma dftMatrix_apply {N : ℕ} (j k : Fin N) :
    dftMatrix N j k = (Real.sqrt N : ℂ)⁻¹ * (zetaN N) ^ ((j : ℕ) * (k : ℕ)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact absurd j.isLt (by simp [hN])
  · have : (zetaN N) ^ ((j : ℕ) * (k : ℕ))
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * (k : ℕ) : ℕ) / (N : ℂ)) := by
      rw [zetaN, ← Complex.exp_nat_mul]
      ring_nf
    rw [dftMatrix, Matrix.of_apply, this]

lemma zetaN_ne_zero {N : ℕ} : zetaN N ≠ 0 := Complex.exp_ne_zero _

/-- Orthogonality of the DFT rows. -/
lemma sum_zetaN_pow {N : ℕ} (hN : 0 < N) (j l : Fin N) :
    ∑ k : Fin N, (zetaN N) ^ ((j : ℕ) * (k : ℕ)) * ((zetaN N) ^ ((l : ℕ) * (k : ℕ)))⁻¹
      = if j = l then (N : ℂ) else 0 := by
  set z := zetaN N with hz
  have hprim : IsPrimitiveRoot z N := isPrimitiveRoot_zetaN hN
  have hz0 : z ≠ 0 := zetaN_ne_zero
  set w : ℂ := z ^ ((j : ℤ) - (l : ℤ)) with hw
  have hterm : ∀ k : Fin N,
      z ^ ((j : ℕ) * (k : ℕ)) * (z ^ ((l : ℕ) * (k : ℕ)))⁻¹ = w ^ (k : ℕ) := by
    intro k
    rw [hw, ← zpow_natCast z ((j : ℕ) * (k : ℕ)), ← zpow_natCast z ((l : ℕ) * (k : ℕ)),
      ← zpow_neg, ← zpow_add₀ hz0, ← zpow_natCast (z ^ ((j : ℤ) - (l : ℤ))) (k : ℕ),
      ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  by_cases hjl : j = l
  · have hw1 : w = 1 := by
      rw [hw, hjl]
      simp
    simp [hw1, hjl]
  · have hwne : w ≠ 1 := by
      intro hw1
      have hdvd : ((N : ℕ) : ℤ) ∣ ((j : ℕ) : ℤ) - ((l : ℕ) : ℤ) :=
        (hprim.zpow_eq_one_iff_dvd _).mp (hw ▸ hw1)
      have hlt : |((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)| < (N : ℤ) := by
        have hj := j.isLt
        have hl := l.isLt
        rw [abs_lt]
        omega
      have h1 : ((j : ℕ) : ℤ) - ((l : ℕ) : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
      apply hjl
      have : (j : ℕ) = (l : ℕ) := by omega
      exact Fin.ext this
    have hsum : ∑ k : Fin N, w ^ (k : ℕ) = ∑ k ∈ Finset.range N, w ^ k := by
      rw [Fin.sum_univ_eq_sum_range (fun k => w ^ k)]
    rw [hsum, geom_sum_eq hwne]
    have hwN : w ^ N = 1 := by
      rw [hw, ← zpow_natCast (z ^ ((j : ℤ) - (l : ℤ))) N, ← zpow_mul, mul_comm,
        zpow_mul, zpow_natCast, hprim.pow_eq_one, one_zpow]
    rw [hwN]
    simp [hjl]

/-- The DFT matrix is unitary. -/
theorem dftMatrix_unitary {N : ℕ} (hN : 0 < N) :
    dftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  have hNr : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hsq : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hNr]
    simp
  have hconj : ∀ k : Fin N,
      (star (dftMatrix N)) k l = (Real.sqrt N : ℂ)⁻¹ * ((zetaN N) ^ ((l : ℕ) * (k : ℕ)))⁻¹ := by
    intro k
    have habs : ‖zetaN N‖ = 1 := by
      have hre : (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)).re = 0 := by
        simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
      simp [zetaN, Complex.norm_exp, hre]
    have hstar : (starRingEnd ℂ) (zetaN N) = (zetaN N)⁻¹ := (Complex.inv_eq_conj habs).symm
    have hs1 : star ((Real.sqrt N : ℂ)⁻¹) = (Real.sqrt N : ℂ)⁻¹ := by
      simp [Complex.conj_ofReal]
    have hs2 : star ((zetaN N) ^ ((l : ℕ) * (k : ℕ))) = ((zetaN N) ^ ((l : ℕ) * (k : ℕ)))⁻¹ := by
      rw [show (star : ℂ → ℂ) = (starRingEnd ℂ) from rfl, map_pow, hstar, inv_pow]
    show star (dftMatrix N l k) = _
    rw [dftMatrix_apply, star_mul', hs1, hs2]
  rw [Matrix.mul_apply]
  simp only [hconj, dftMatrix_apply]
  have : ∀ k : Fin N,
      ((Real.sqrt N : ℂ)⁻¹ * (zetaN N) ^ ((j : ℕ) * (k : ℕ))) *
        ((Real.sqrt N : ℂ)⁻¹ * ((zetaN N) ^ ((l : ℕ) * (k : ℕ)))⁻¹)
      = (N : ℂ)⁻¹ * ((zetaN N) ^ ((j : ℕ) * (k : ℕ)) * ((zetaN N) ^ ((l : ℕ) * (k : ℕ)))⁻¹) := by
    intro k
    have h2 : (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
      rw [← mul_inv, hsq]
    rw [← h2]
    ring
  rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, sum_zetaN_pow hN]
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  by_cases hjl : j = l <;> simp [hjl, Matrix.one_apply, hNne]

/-- The `n`-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary (n : ℕ) : qft n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  dftMatrix_unitary (Nat.two_pow_pos n)

end QC

