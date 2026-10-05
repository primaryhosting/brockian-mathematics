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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The `n`-dimensional quantum Fourier transform matrix:
`(qftMatrix n) i j = exp (2 π I * (i * j) / n) / √n`.
For `n = 2 ^ 7` this is the 7-qubit QFT. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j =>
    Complex.exp (2 * Real.pi * Complex.I * ((i : ℕ) * (j : ℕ) : ℕ) / n) / Real.sqrt n

/-- The primitive `n`-th root of unity used by the QFT. -/
noncomputable def qftRoot (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

theorem qftRoot_isPrimitiveRoot {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (qftRoot n) n :=
  Complex.isPrimitiveRoot_exp n hn

theorem qftMatrix_apply {n : ℕ} (i j : Fin n) :
    qftMatrix n i j = qftRoot n ^ ((i : ℕ) * (j : ℕ)) / Real.sqrt n := by
  simp only [qftMatrix, Matrix.of_apply, qftRoot, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem qftRoot_ne_zero (n : ℕ) : qftRoot n ≠ 0 := Complex.exp_ne_zero _

theorem norm_qftRoot_pow (n m : ℕ) : ‖qftRoot n ^ m‖ = 1 := by
  rw [norm_pow, qftRoot, Complex.norm_exp]
  norm_num [Complex.div_re, Complex.mul_re, Complex.mul_im]

theorem conj_qftRoot_pow (n m : ℕ) :
    (starRingEnd ℂ) (qftRoot n ^ m) = (qftRoot n ^ m)⁻¹ :=
  (Complex.inv_eq_conj (norm_qftRoot_pow n m)).symm

/-- The geometric sum of `n`-th roots of unity: it equals `n` when the two indices agree
and vanishes otherwise. -/
theorem qft_geom_sum {n : ℕ} (hn : n ≠ 0) (i j : Fin n) :
    ∑ k : Fin n, (qftRoot n ^ (i : ℕ) * (qftRoot n ^ (j : ℕ))⁻¹) ^ (k : ℕ)
      = if i = j then (n : ℂ) else 0 := by
  set z := qftRoot n with hz
  set w : ℂ := z ^ (i : ℕ) * (z ^ (j : ℕ))⁻¹ with hw
  have hzne : z ≠ 0 := qftRoot_ne_zero n
  have hzn : z ^ n = 1 := (qftRoot_isPrimitiveRoot hn).pow_eq_one
  rw [Fin.sum_univ_eq_sum_range (fun k => w ^ k) n]
  by_cases hij : i = j
  · have hw1 : w = 1 := by
      rw [hw, hij]
      field_simp
    simp [hw1, hij]
  · have hw1 : w ≠ 1 := by
      intro h
      apply hij
      have hpow : z ^ (i : ℕ) = z ^ (j : ℕ) := by
        rw [hw] at h
        field_simp at h
        exact h
      exact Fin.ext ((qftRoot_isPrimitiveRoot hn).pow_inj i.isLt j.isLt hpow)
    have hwn : w ^ n = 1 := by
      rw [hw, mul_pow, ← pow_mul, ← inv_pow, ← pow_mul, mul_comm (i : ℕ) n,
        mul_comm (j : ℕ) n, pow_mul, pow_mul, hzn]
      simp [hzn]
    rw [geom_sum_eq hw1, hwn]
    simp [hij]

/-- The `n`-dimensional QFT matrix is unitary (for `n ≠ 0`). -/
theorem qftMatrix_unitary {n : ℕ} (hn : n ≠ 0) :
    qftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hsq : ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n)]
    simp
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin n, qftMatrix n i k * (star (qftMatrix n)) k j
      = (qftRoot n ^ (i : ℕ) * (qftRoot n ^ (j : ℕ))⁻¹) ^ (k : ℕ) / n := by
    intro k
    have h1 : qftMatrix n i k = qftRoot n ^ ((i : ℕ) * (k : ℕ)) / (Real.sqrt n : ℝ) :=
      qftMatrix_apply i k
    have h2 : (star (qftMatrix n)) k j
        = (qftRoot n ^ ((j : ℕ) * (k : ℕ)))⁻¹ / (Real.sqrt n : ℝ) := by
      rw [Matrix.star_apply, qftMatrix_apply, Complex.star_def, map_div₀, conj_qftRoot_pow,
        Complex.conj_ofReal]
    rw [h1, h2, div_mul_div_comm, hsq]
    congr 1
    rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul]
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.sum_div, qft_geom_sum hn i j]
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply, hnC]

/-- The 7-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary_7 : qftMatrix (2 ^ 7) ∈ Matrix.unitaryGroup (Fin (2 ^ 7)) ℂ :=
  qftMatrix_unitary (by norm_num)

end QC

