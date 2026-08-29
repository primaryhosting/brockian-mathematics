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

namespace QC

open Complex Matrix Finset

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The `n`-dimensional discrete Fourier transform (QFT) matrix:
`F j k = ω^(j*k) / √n` with `ω = exp (2 π i / n)`. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => zeta n ^ ((j : ℕ) * (k : ℕ)) / (Real.sqrt n : ℂ)

lemma norm_zeta (n : ℕ) : ‖zeta n‖ = 1 := by
  simp [zeta, Complex.norm_exp]

lemma zeta_pow_n (n : ℕ) (hn : n ≠ 0) : zeta n ^ n = 1 :=
  (Complex.isPrimitiveRoot_exp n hn).pow_eq_one

lemma zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := by
  intro h
  have := norm_zeta n
  rw [h] at this
  simp at this

/-- The key orthogonality relation for the columns of the QFT matrix. -/
lemma sum_zeta_orthogonality (n : ℕ) (hn : n ≠ 0) (k l : Fin n) :
    ∑ j : Fin n, (starRingEnd ℂ) (zeta n ^ ((j : ℕ) * (k : ℕ))) * zeta n ^ ((j : ℕ) * (l : ℕ))
      = if k = l then (n : ℂ) else 0 := by
  set x : ℂ := (zeta n ^ (k : ℕ))⁻¹ * zeta n ^ (l : ℕ) with hx
  have hterm : ∀ j : ℕ,
      (starRingEnd ℂ) (zeta n ^ (j * (k : ℕ))) * zeta n ^ (j * (l : ℕ)) = x ^ j := by
    intro j
    have hnorm : ‖zeta n ^ (j * (k : ℕ))‖ = 1 := by rw [norm_pow, norm_zeta, one_pow]
    have h1 : (starRingEnd ℂ) (zeta n ^ (j * (k : ℕ))) = (zeta n ^ (j * (k : ℕ)))⁻¹ :=
      (Complex.inv_eq_conj hnorm).symm
    rw [h1, hx, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (k : ℕ) j,
      mul_comm (l : ℕ) j]
  have hxn : x ^ n = 1 := by
    rw [hx, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (k : ℕ) n, mul_comm (l : ℕ) n,
      pow_mul, pow_mul, zeta_pow_n n hn]
    simp
  have hsum : ∑ j : Fin n, (starRingEnd ℂ) (zeta n ^ ((j : ℕ) * (k : ℕ)))
      * zeta n ^ ((j : ℕ) * (l : ℕ)) = ∑ j ∈ Finset.range n, x ^ j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => x ^ j) n]
    exact Finset.sum_congr rfl (fun j _ => hterm (j : ℕ))
  rw [hsum]
  by_cases hkl : k = l
  · have hx1 : x = 1 := by
      rw [hx, hkl]
      exact inv_mul_cancel₀ (pow_ne_zero _ (zeta_ne_zero n))
    simp [hx1, hkl]
  · have hx1 : x ≠ 1 := by
      intro h
      apply hkl
      have h' : (zeta n ^ (k : ℕ))⁻¹ * zeta n ^ (l : ℕ) = 1 := by rw [← hx]; exact h
      have : zeta n ^ (k : ℕ) = zeta n ^ (l : ℕ) :=
        (inv_mul_eq_one₀ (pow_ne_zero _ (zeta_ne_zero n))).mp h'
      exact Fin.ext ((Complex.isPrimitiveRoot_exp n hn).pow_inj k.isLt l.isLt this)
    rw [geom_sum_eq hx1, hxn, if_neg hkl]
    simp

/-- The `n`-dimensional QFT matrix is unitary for every `n > 0`. -/
theorem qft_unitary (n : ℕ) (hn : n ≠ 0) : qftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hs : (Real.sqrt n : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr hnpos)
  have hsq : (Real.sqrt n : ℂ) * (Real.sqrt n : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hnpos)]
    simp
  have hstar : (qftMatrix n)ᴴ * qftMatrix n = 1 := by
    ext k l
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, qftMatrix, Matrix.of_apply]
    have : ∀ j : Fin n,
        star (zeta n ^ ((j : ℕ) * (k : ℕ)) / (Real.sqrt n : ℂ))
          * (zeta n ^ ((j : ℕ) * (l : ℕ)) / (Real.sqrt n : ℂ))
        = ((starRingEnd ℂ) (zeta n ^ ((j : ℕ) * (k : ℕ)))
            * zeta n ^ ((j : ℕ) * (l : ℕ))) / (n : ℂ) := by
      intro j
      simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
      rw [div_mul_div_comm, hsq]
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_div,
      sum_zeta_orthogonality n hn k l]
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    by_cases hkl : k = l <;> simp [hkl, Matrix.one_apply, hn']
  rw [Matrix.mem_unitaryGroup_iff]
  have : star (qftMatrix n) = (qftMatrix n)ᴴ := rfl
  rw [this, mul_eq_one_comm]
  exact hstar

/-- **The 8-qubit QFT matrix is unitary.**
The quantum Fourier transform on an 8-qubit register acts on a `2^8 = 256`-dimensional
state space, with matrix entries `F j k = exp (2 π i j k / 2^8) / √(2^8)`. -/
theorem qft_unitary_8 : qftMatrix (2 ^ 8) ∈ Matrix.unitaryGroup (Fin (2 ^ 8)) ℂ :=
  qft_unitary (2 ^ 8) (by norm_num)

/-- The QFT matrix in dimension `8` is unitary. -/
theorem qft_unitary_dim8 : qftMatrix 8 ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  qft_unitary 8 (by norm_num)

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

