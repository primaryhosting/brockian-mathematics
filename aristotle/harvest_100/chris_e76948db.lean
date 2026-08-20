/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# The quantum Fourier transform is unitary

We define the `n`-point discrete/quantum Fourier transform matrix

`qftMatrix n = (1/√n) * (ω^(j*k))_{j,k}` with `ω = exp (2πi/n)`,

prove it is unitary for every `n ≠ 0`, and specialize to the 4-qubit case `n = 2^4 = 16`,
giving the target theorem `QC.qft_unitary_4`.
-/

namespace QC

open Complex Matrix Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℕ))

lemma zeta_isPrimitiveRoot (n : ℕ) [NeZero n] : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n (NeZero.ne n)

lemma zeta_pow_self (n : ℕ) [NeZero n] : zeta n ^ n = 1 :=
  (zeta_isPrimitiveRoot n).pow_eq_one

lemma zeta_ne_zero (n : ℕ) [NeZero n] : zeta n ≠ 0 := by
  intro h
  have hn := zeta_pow_self n
  rw [h, zero_pow (NeZero.ne n)] at hn
  exact zero_ne_one hn

lemma zeta_norm (n : ℕ) [NeZero n] : ‖zeta n‖ = 1 := by
  have h : ‖zeta n‖ ^ n = 1 := by rw [← norm_pow, zeta_pow_self n, norm_one]
  rcases lt_trichotomy ‖zeta n‖ 1 with hlt | heq | hgt
  · have := pow_lt_one₀ (norm_nonneg (zeta n)) hlt (NeZero.ne n)
    rw [h] at this
    exact absurd this (lt_irrefl 1)
  · exact heq
  · have := one_lt_pow₀ hgt (NeZero.ne n)
    rw [h] at this
    exact absurd this (lt_irrefl 1)

lemma star_zeta (n : ℕ) [NeZero n] : star (zeta n) = (zeta n)⁻¹ :=
  (Complex.inv_eq_conj (zeta_norm n)).symm

/-- The geometric sum `∑_{k<n} (ζₙ^d)^k` vanishes whenever `n ∤ d`. -/
lemma zeta_geom_sum (n : ℕ) [NeZero n] (d : ℤ) (hd : ¬ ((n : ℤ) ∣ d)) :
    ∑ k ∈ Finset.range n, (zeta n ^ d) ^ (k : ℕ) = 0 := by
  have hne : zeta n ^ d ≠ 1 := fun h =>
    hd (((zeta_isPrimitiveRoot n).zpow_eq_one_iff_dvd d).mp h)
  have hpow : (zeta n ^ d) ^ n = 1 := by
    rw [← zpow_natCast (zeta n ^ d) n, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, zeta_pow_self n, _root_.one_zpow]
  rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- Splitting a power of `ζₙ` indexed by a difference of exponents. -/
lemma zeta_pow_sub (n : ℕ) [NeZero n] (a b c : ℕ) :
    zeta n ^ (a * c) * (zeta n)⁻¹ ^ (b * c) = (zeta n ^ ((a : ℤ) - b)) ^ c := by
  rw [← zpow_natCast (zeta n ^ ((a : ℤ) - b)) c, ← _root_.zpow_mul, sub_mul,
    zpow_sub₀ (zeta_ne_zero n), inv_pow, ← zpow_natCast (zeta n) (a * c),
    ← zpow_natCast (zeta n) (b * c), div_eq_mul_inv]
  push_cast
  ring

/-- The `n`-point quantum Fourier transform matrix: `(1/√n) · ω^(j·k)` with `ω = exp (2πi/n)`. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => ((1 / Real.sqrt n : ℝ) : ℂ) * zeta n ^ (j.val * k.val)

/-- The rows of the QFT matrix are orthonormal. -/
lemma qftMatrix_mul_conjTranspose (n : ℕ) [NeZero n] :
    qftMatrix n * (qftMatrix n)ᴴ = 1 := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hnorm : ((1 / Real.sqrt n : ℝ) : ℂ) * ((1 / Real.sqrt n : ℝ) : ℂ)
      = ((1 / n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp [Real.sqrt_ne_zero'.mpr hnpos]
    exact (Real.sq_sqrt hnpos.le).symm
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin n, qftMatrix n j k * (qftMatrix n)ᴴ k l
      = ((1 / n : ℝ) : ℂ) * (zeta n ^ ((j : ℤ) - (l : ℤ))) ^ (k : ℕ) := by
    intro k
    simp only [qftMatrix, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_pow,
      star_zeta, Complex.star_def, Complex.conj_ofReal]
    rw [← zeta_pow_sub n j.val l.val k.val, ← hnorm]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun k => (zeta n ^ ((j : ℤ) - (l : ℤ))) ^ k) n]
  by_cases h : j = l
  · subst h
    rw [if_pos rfl]
    simp only [sub_self, zpow_zero, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, one_div,
      inv_mul_cancel₀ (ne_of_gt hnpos), Complex.ofReal_one]
  · rw [if_neg h, zeta_geom_sum, mul_zero]
    have hj := j.isLt
    have hl := l.isLt
    have hne : (j : ℕ) ≠ (l : ℕ) := fun hc => h (Fin.ext hc)
    intro hdvd
    have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; omega)
    omega

/-- **The `n`-point quantum Fourier transform matrix is unitary** (for `n ≠ 0`). -/
theorem qftMatrix_unitary (n : ℕ) [NeZero n] : qftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr (qftMatrix_mul_conjTranspose n)

/-- The 4-qubit quantum Fourier transform matrix, of size `2^4 = 16`. -/
noncomputable def qft4 : Matrix (Fin 16) (Fin 16) ℂ := qftMatrix 16

/-- The entries of the 4-qubit QFT matrix: `(1/4) · exp (2πi/16)^(j·k)`. -/
lemma qft4_apply (j k : Fin 16) :
    qft4 j k = (1 / 4 : ℂ) * Complex.exp (2 * Real.pi * Complex.I / 16) ^ (j.val * k.val) := by
  have h : Real.sqrt (16 : ℕ) = 4 := by
    rw [show ((16 : ℕ) : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [qft4, qftMatrix, zeta, Matrix.of_apply, h]
  norm_num

/-- **The 4-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary_4 : qft4 ∈ Matrix.unitaryGroup (Fin 16) ℂ := qftMatrix_unitary 16

/-- The unitarity of the 4-qubit QFT, spelled out as `Uᴴ * U = 1` and `U * Uᴴ = 1`. -/
theorem qft_unitary_4' : qft4ᴴ * qft4 = 1 ∧ qft4 * qft4ᴴ = 1 :=
  ⟨Matrix.mem_unitaryGroup_iff'.mp qft_unitary_4, qftMatrix_mul_conjTranspose 16⟩

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

