import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The primitive `16`-th root of unity `e^{2πi/16}` used by the 4-qubit QFT
(`N = 2^4 = 16`). -/
noncomputable def omega16 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The 4-qubit quantum Fourier transform matrix, acting on the `2^4 = 16`
dimensional state space: `(QFT)_{j,k} = ω^{jk} / √16 = ω^{jk} / 4`. -/
noncomputable def qft4 : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun j k => omega16 ^ ((j : ℕ) * (k : ℕ)) / 4

lemma isPrimitiveRoot_omega16 : IsPrimitiveRoot omega16 16 := by
  have := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  simpa [omega16] using this

lemma omega16_pow_16 : omega16 ^ 16 = 1 := isPrimitiveRoot_omega16.pow_eq_one

lemma star_omega16 : star omega16 = omega16⁻¹ := by
  show (starRingEnd ℂ) omega16 = _
  rw [omega16, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]
  ring

/-- For `k l : Fin 16`, the ratio `ω^k * (ω^l)⁻¹` is a 16-th root of unity. -/
lemma ratio_pow_16 (k l : Fin 16) :
    (omega16 ^ (k : ℕ) * (omega16 ^ (l : ℕ))⁻¹) ^ 16 = 1 := by
  rw [mul_pow, ← pow_mul, ← inv_pow, ← pow_mul]
  rw [mul_comm (k : ℕ) 16, mul_comm (l : ℕ) 16, pow_mul, pow_mul, omega16_pow_16]
  simp [omega16_pow_16]

/-- The ratio equals `1` exactly when the two indices coincide. -/
lemma ratio_eq_one_iff (k l : Fin 16) :
    omega16 ^ (k : ℕ) * (omega16 ^ (l : ℕ))⁻¹ = 1 ↔ k = l := by
  have hne : omega16 ^ (l : ℕ) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  constructor
  · intro h
    have : omega16 ^ (k : ℕ) = omega16 ^ (l : ℕ) := by
      field_simp at h
      exact h
    exact Fin.ext (isPrimitiveRoot_omega16.pow_inj k.isLt l.isLt this)
  · rintro rfl
    field_simp

/-- The key orthogonality relation: the geometric sum of the ratio over all
`16` indices is `16` when `k = l` and `0` otherwise. -/
lemma sum_ratio (k l : Fin 16) :
    ∑ j : Fin 16, (omega16 ^ (k : ℕ) * (omega16 ^ (l : ℕ))⁻¹) ^ (j : ℕ)
      = if k = l then (16 : ℂ) else 0 := by
  set z : ℂ := omega16 ^ (k : ℕ) * (omega16 ^ (l : ℕ))⁻¹ with hz
  rw [Fin.sum_univ_eq_sum_range (fun j => z ^ j) 16]
  by_cases h : k = l
  · subst h
    have hz1 : z = 1 := (ratio_eq_one_iff k k).2 rfl
    simp [hz1]
  · have hz1 : z ≠ 1 := fun hc => h ((ratio_eq_one_iff k l).1 hc)
    rw [geom_sum_eq hz1, ratio_pow_16 k l]
    simp [h]

/-- **The 4-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary_4 : qft4 ∈ Matrix.unitaryGroup (Fin 16) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext k l
  rw [Matrix.mul_apply]
  have hstep : ∀ j : Fin 16,
      qft4 k j * (star qft4) j l
        = (1 / 16 : ℂ) * (omega16 ^ (k : ℕ) * (omega16 ^ (l : ℕ))⁻¹) ^ (j : ℕ) := by
    intro j
    rw [Matrix.star_apply, qft4]
    simp only [Matrix.of_apply]
    rw [star_div₀, star_pow, star_omega16]
    have : (star (4 : ℂ)) = 4 := by simp
    rw [this]
    rw [mul_pow, ← pow_mul, ← inv_pow, ← pow_mul]
    rw [mul_comm (k : ℕ) (j : ℕ), mul_comm (l : ℕ) (j : ℕ)]
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun j _ => hstep j), ← Finset.mul_sum, sum_ratio k l]
  by_cases h : k = l <;> simp [h, Matrix.one_apply]

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

