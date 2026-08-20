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
