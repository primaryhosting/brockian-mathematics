/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
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

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/
noncomputable def zeta (N : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

/-- The `N × N` quantum Fourier transform matrix,
`(QFT_N)_{j,k} = N^{-1/2} · exp (2πi·j·k/N)`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    ((Real.sqrt N : ℝ) : ℂ)⁻¹ *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * (k : ℕ) : ℕ) / (N : ℂ))

lemma qftMatrix_apply (N : ℕ) (j k : Fin N) :
    qftMatrix N j k = ((Real.sqrt N : ℝ) : ℂ)⁻¹ * (zeta N) ^ ((j : ℕ) * (k : ℕ)) := by
  unfold qftMatrix zeta
  simp only [Matrix.of_apply]
  rw [← Complex.exp_nat_mul]
  ring_nf

lemma zeta_isPrimitiveRoot (N : ℕ) (hN : N ≠ 0) : IsPrimitiveRoot (zeta N) N :=
  Complex.isPrimitiveRoot_exp N hN

lemma zeta_ne_zero (N : ℕ) : zeta N ≠ 0 := Complex.exp_ne_zero _

lemma zeta_pow_N (N : ℕ) (hN : N ≠ 0) : (zeta N) ^ N = 1 :=
  (zeta_isPrimitiveRoot N hN).pow_eq_one

lemma conj_zeta (N : ℕ) : (starRingEnd ℂ) (zeta N) = (zeta N)⁻¹ := by
  unfold zeta
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.conj_I, map_ofNat]
  ring

/-- Orthogonality of the columns of the QFT matrix. -/
lemma qft_orthogonality (N : ℕ) (hN : N ≠ 0) (k l : Fin N) :
    ∑ j : Fin N, (starRingEnd ℂ) (qftMatrix N j k) * qftMatrix N j l =
      if k = l then 1 else 0 := by
  have hz : zeta N ≠ 0 := zeta_ne_zero N
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hs : ((Real.sqrt N : ℝ) : ℂ) ^ 2 = (N : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hNpos.le
  have hsne : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := by
    simpa using (Real.sqrt_pos.mpr hNpos).ne'
  set w : ℂ := (zeta N) ^ (l : ℕ) * ((zeta N)⁻¹) ^ (k : ℕ) with hw
  have key : ∀ j : Fin N,
      (starRingEnd ℂ) (qftMatrix N j k) * qftMatrix N j l = ((N : ℂ))⁻¹ * w ^ (j : ℕ) := by
    intro j
    rw [qftMatrix_apply, qftMatrix_apply, map_mul, map_pow, conj_zeta, map_inv₀,
      Complex.conj_ofReal, hw, mul_pow, ← pow_mul, ← pow_mul,
      show (l : ℕ) * (j : ℕ) = (j : ℕ) * (l : ℕ) from Nat.mul_comm _ _,
      show (k : ℕ) * (j : ℕ) = (j : ℕ) * (k : ℕ) from Nat.mul_comm _ _, ← hs]
    field_simp
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun i => w ^ i) N]
  have hwN : w ^ N = 1 := by
    rw [hw, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (l : ℕ) N,
      Nat.mul_comm (k : ℕ) N, pow_mul, pow_mul, inv_pow, zeta_pow_N N hN]
    simp
  by_cases hkl : k = l
  · subst hkl
    have hw1 : w = 1 := by
      rw [hw, ← mul_pow, mul_inv_cancel₀ hz, one_pow]
    simp only [hw1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [if_true]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN : (N : ℂ) ≠ 0)
  · have hw1 : w ≠ 1 := by
      intro h
      apply hkl
      have hlk : (zeta N) ^ (l : ℕ) = (zeta N) ^ (k : ℕ) := by
        rw [hw, inv_pow] at h
        field_simp at h
        exact h
      have := (zeta_isPrimitiveRoot N hN).pow_inj l.isLt k.isLt hlk
      exact (Fin.ext this).symm
    rw [geom_sum_eq hw1, hwN, if_neg hkl]
    simp

/-- The `N × N` QFT matrix is unitary, for any `N ≠ 0`. -/
theorem qft_unitary (N : ℕ) (hN : N ≠ 0) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext k l
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, RCLike.star_def]
  exact qft_orthogonality N hN k l

/-- The 6-qubit QFT matrix (of size `2^6 = 64`) is unitary. -/
theorem qft_unitary_6 : qftMatrix (2 ^ 6) ∈ Matrix.unitaryGroup (Fin (2 ^ 6)) ℂ :=
  qft_unitary (2 ^ 6) (by norm_num)

end QC

