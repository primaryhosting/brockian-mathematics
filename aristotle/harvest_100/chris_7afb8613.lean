/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
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

set_option grind.warning false

namespace QC

/-- The primitive `32`-nd root of unity used by the 5-qubit quantum Fourier transform. -/
noncomputable def qftOmega5 : ℂ := Complex.exp (2 * Real.pi * Complex.I / (32 : ℕ))

/-- The 5-qubit quantum Fourier transform matrix, of size `2 ^ 5 = 32`:
`F j k = ω ^ (j * k) / √32` with `ω = exp (2 π i / 32)`. -/
noncomputable def qftMatrix5 : Matrix (Fin 32) (Fin 32) ℂ :=
  fun j k => (Real.sqrt 32 : ℂ)⁻¹ * qftOmega5 ^ (j.val * k.val)

lemma qftOmega5_primitive : IsPrimitiveRoot qftOmega5 32 :=
  Complex.isPrimitiveRoot_exp 32 (by norm_num)

lemma qftOmega5_norm : ‖qftOmega5‖ = 1 := by
  simp [qftOmega5, Complex.norm_exp]

lemma qftOmega5_ne_zero : qftOmega5 ≠ 0 := by
  intro h
  have hn := qftOmega5_norm
  rw [h] at hn
  simp at hn

lemma conj_qftOmega5_pow (m : ℕ) :
    (starRingEnd ℂ) (qftOmega5 ^ m) = (qftOmega5 ^ m)⁻¹ := by
  have h : ‖qftOmega5 ^ m‖ = 1 := by
    rw [norm_pow, qftOmega5_norm, one_pow]
  rw [Complex.inv_eq_conj h]

/-- Orthogonality relations for the columns of the QFT matrix. -/
lemma qft5_column_orthogonality (j k : Fin 32) :
    ∑ l : Fin 32, (qftOmega5 ^ (l.val * j.val))⁻¹ * qftOmega5 ^ (l.val * k.val)
      = if j = k then (32 : ℂ) else 0 := by
  have hne : qftOmega5 ^ j.val ≠ 0 := pow_ne_zero _ qftOmega5_ne_zero
  set r : ℂ := qftOmega5 ^ k.val * (qftOmega5 ^ j.val)⁻¹ with hr
  have hterm : ∀ l : Fin 32,
      (qftOmega5 ^ (l.val * j.val))⁻¹ * qftOmega5 ^ (l.val * k.val) = r ^ l.val := by
    intro l
    rw [hr, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k.val l.val, mul_comm j.val l.val]
    ring
  rw [Finset.sum_congr rfl (fun l _ => hterm l), Fin.sum_univ_eq_sum_range (fun i => r ^ i) 32]
  have hone : qftOmega5 ^ (32 : ℕ) = 1 := qftOmega5_primitive.pow_eq_one
  have hr32 : r ^ 32 = 1 := by
    rw [hr, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k.val 32, mul_comm j.val 32,
      pow_mul, pow_mul, hone, one_pow, one_pow, inv_one, mul_one]
  by_cases hjk : j = k
  · have hr1 : r = 1 := by
      rw [hr, hjk, mul_inv_cancel₀ (by rw [← hjk]; exact hne)]
    simp [hr1, hjk]
  · have hrne : r ≠ 1 := by
      intro h
      rw [hr, ← div_eq_mul_inv, div_eq_one_iff_eq hne] at h
      exact hjk (Fin.ext (qftOmega5_primitive.pow_inj k.isLt j.isLt h)).symm
    rw [geom_sum_eq hrne, hr32]
    simp [hjk]

/-- The 5-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary_5 : qftMatrix5 ∈ Matrix.unitaryGroup (Fin 32) ℂ := by
  have hsq : ((Real.sqrt 32 : ℂ))⁻¹ * ((Real.sqrt 32 : ℂ))⁻¹ = (32 : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 32)]
    norm_num
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply]
  have hterm : ∀ l : Fin 32, (star qftMatrix5) j l * qftMatrix5 l k
      = (32 : ℂ)⁻¹ * ((qftOmega5 ^ (l.val * j.val))⁻¹ * qftOmega5 ^ (l.val * k.val)) := by
    intro l
    simp only [Matrix.star_apply, qftMatrix5, Complex.star_def, map_mul, map_inv₀,
      Complex.conj_ofReal, conj_qftOmega5_pow]
    rw [← hsq]
    ring
  rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.mul_sum,
    qft5_column_orthogonality j k]
  by_cases hjk : j = k
  · subst hjk
    rw [Matrix.one_apply_eq]
    norm_num
  · rw [Matrix.one_apply_ne hjk]
    simp [hjk]

end QC

