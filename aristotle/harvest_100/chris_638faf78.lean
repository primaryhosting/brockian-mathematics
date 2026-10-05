/-
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
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

open Complex Matrix

/-- The primitive `8`-th root of unity `ω = e^{2πi/8}` used by the 3-qubit QFT. -/
noncomputable def zeta8 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

lemma isPrimitiveRoot_zeta8 : IsPrimitiveRoot zeta8 8 := by
  have h := Complex.isPrimitiveRoot_exp 8 (by norm_num)
  simpa [zeta8] using h

lemma zeta8_pow_eight : zeta8 ^ 8 = 1 := isPrimitiveRoot_zeta8.pow_eq_one

lemma zeta8_ne_zero : zeta8 ≠ 0 := Complex.exp_ne_zero _

lemma conj_zeta8 : (starRingEnd ℂ) zeta8 = zeta8 ^ 7 := by
  have h1 : zeta8 * (starRingEnd ℂ) zeta8 = 1 := by
    rw [zeta8, ← Complex.exp_conj, ← Complex.exp_add]
    have h : (2 * (Real.pi : ℂ) * Complex.I / 8)
        + (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / 8) = 0 := by
      simp [map_div₀, Complex.conj_ofReal, Complex.conj_ofNat]
      ring
    rw [h, Complex.exp_zero]
  have h2 : zeta8 * zeta8 ^ 7 = 1 := by
    rw [← pow_succ']
    exact zeta8_pow_eight
  exact mul_left_cancel₀ zeta8_ne_zero (h1.trans h2.symm)

/-- Geometric sum over the eight powers of an eighth root of unity. -/
lemma sum_pow_eight (w : ℂ) (hw : w ^ 8 = 1) :
    ∑ l : Fin 8, w ^ (l : ℕ) = if w = 1 then 8 else 0 := by
  by_cases h : w = 1
  · simp [h]
  · rw [if_neg h, Fin.sum_univ_eq_sum_range (fun i => w ^ i) 8, geom_sum_eq h, hw]
    simp

/-- The 3-qubit quantum Fourier transform matrix:
`(QFT₃)_{j,k} = ω^{jk} / √8` with `ω = e^{2πi/8}`. -/
noncomputable def qft3 : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun j k => ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * zeta8 ^ (j.val * k.val)

lemma inv_sqrt8_sq : ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ = (8 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma zeta8_pow_mod (a : ℕ) : zeta8 ^ a = zeta8 ^ (a % 8) := by
  conv_lhs => rw [← Nat.div_add_mod a 8]
  rw [pow_add, pow_mul, zeta8_pow_eight, one_pow, one_mul]

/-- **The 3-qubit QFT matrix is unitary.** -/
theorem qft_unitary_3 : qft3ᴴ * qft3 = 1 ∧ qft3 * qft3ᴴ = 1 := by
  have key : qft3ᴴ * qft3 = 1 := by
    ext j k
    rw [Matrix.mul_apply]
    have hterm : ∀ l : Fin 8, qft3ᴴ j l * qft3 l k
        = (8 : ℂ)⁻¹ * (zeta8 ^ (7 * j.val + k.val)) ^ (l : ℕ) := by
      intro l
      simp only [Matrix.conjTranspose_apply, qft3, Matrix.of_apply, Complex.star_def, map_mul,
        map_inv₀, Complex.conj_ofReal, map_pow, conj_zeta8]
      rw [mul_mul_mul_comm, inv_sqrt8_sq, ← pow_mul, ← pow_mul, ← pow_add]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.mul_sum,
      sum_pow_eight _ (by rw [← pow_mul, mul_comm, pow_mul, zeta8_pow_eight, one_pow])]
    by_cases hjk : j = k
    · subst hjk
      have h1 : zeta8 ^ (7 * j.val + j.val) = 1 := by
        have h2 : 7 * j.val + j.val = 8 * j.val := by ring
        rw [h2, pow_mul, zeta8_pow_eight, one_pow]
      rw [h1, if_pos rfl, Matrix.one_apply_eq]
      norm_num
    · have hjk' : j.val ≠ k.val := fun hh => hjk (Fin.ext hh)
      have hj := j.isLt
      have hk := k.isLt
      have hne : zeta8 ^ (7 * j.val + k.val) ≠ 1 := by
        rw [zeta8_pow_mod]
        exact isPrimitiveRoot_zeta8.pow_ne_one_of_pos_of_lt (by omega) (by omega)
      rw [if_neg hne, Matrix.one_apply_ne hjk]
      ring
  exact ⟨key, mul_eq_one_comm.mp key⟩

/-- Restatement: the 3-qubit QFT matrix belongs to the unitary group. -/
theorem qft3_mem_unitaryGroup : qft3 ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  ⟨qft_unitary_3.1, qft_unitary_3.2⟩

end QC

