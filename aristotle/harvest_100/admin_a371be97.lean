import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- The primitive `16`-th root of unity `exp (2πi/16)` used to build the 4-qubit QFT. -/
noncomputable def qftZeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The `16 × 16` matrix of the quantum Fourier transform on 4 qubits:
`Q j k = (1/4) * exp (2πi j k / 16)`. -/
noncomputable def qft4 : Matrix (Fin 16) (Fin 16) ℂ :=
  fun j k => (1 / 4 : ℂ) * qftZeta ^ (j.val * k.val)

lemma qftZeta_isPrimitiveRoot : IsPrimitiveRoot qftZeta 16 := by
  have h := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  simpa [qftZeta, mul_comm, mul_assoc, mul_left_comm] using h

lemma qftZeta_ne_zero : qftZeta ≠ 0 := Complex.exp_ne_zero _

lemma qftZeta_pow_sixteen : qftZeta ^ (16 : ℕ) = 1 := qftZeta_isPrimitiveRoot.pow_eq_one

lemma conj_qftZeta : (starRingEnd ℂ) qftZeta = qftZeta⁻¹ := by
  rw [qftZeta, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.conj_I, map_ofNat]
  ring

lemma conj_qftZeta_pow (m : ℕ) : (starRingEnd ℂ) (qftZeta ^ m) = (qftZeta ^ m)⁻¹ := by
  rw [map_pow, conj_qftZeta, inv_pow]

/-- The orthogonality relation for the 16-th roots of unity. -/
lemma qft_sum (j k : Fin 16) :
    ∑ n : Fin 16, qftZeta ^ (j.val * n.val) * (starRingEnd ℂ) (qftZeta ^ (k.val * n.val))
      = if j = k then (16 : ℂ) else 0 := by
  set d : ℤ := (j.val : ℤ) - (k.val : ℤ) with hd
  have hterm : ∀ n : Fin 16,
      qftZeta ^ (j.val * n.val) * (starRingEnd ℂ) (qftZeta ^ (k.val * n.val))
        = (qftZeta ^ d) ^ (n.val) := by
    intro n
    rw [conj_qftZeta_pow, ← zpow_natCast qftZeta (j.val * n.val),
      ← zpow_natCast qftZeta (k.val * n.val), ← zpow_neg, ← zpow_add₀ qftZeta_ne_zero,
      ← zpow_natCast (qftZeta ^ d) n.val, ← zpow_mul]
    congr 1
    push_cast [hd]
    ring
  rw [Finset.sum_congr rfl (fun n _ => hterm n)]
  by_cases hjk : j = k
  · subst hjk
    have : d = 0 := by simp [hd]
    simp [this]
  · have hd0 : d ≠ 0 := by
      simp only [hd, sub_ne_zero]
      exact_mod_cast fun h => hjk (Fin.ext (by exact_mod_cast h))
    have hdlt : d < 16 := by
      have : (j.val : ℤ) < 16 := by exact_mod_cast j.isLt
      omega
    have hdgt : -16 < d := by
      have : (k.val : ℤ) < 16 := by exact_mod_cast k.isLt
      omega
    have hnd : ¬ ((16 : ℤ) ∣ d) := by
      intro h
      obtain ⟨c, hc⟩ := h
      omega
    have hne1 : qftZeta ^ d ≠ 1 := by
      intro h
      exact hnd ((qftZeta_isPrimitiveRoot.zpow_eq_one_iff_dvd d).mp h)
    have hpow : (qftZeta ^ d) ^ (16 : ℕ) = 1 := by
      rw [← zpow_natCast (qftZeta ^ d) 16, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, qftZeta_pow_sixteen, one_zpow]
    rw [Fin.sum_univ_eq_sum_range (fun n => (qftZeta ^ d) ^ n) 16,
      geom_sum_eq hne1, hpow, sub_self, zero_div]
    simp [hjk]

/-- **The 4-qubit QFT matrix is unitary.** -/
theorem qft_unitary_4 : qft4 ∈ Matrix.unitaryGroup (Fin 16) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext j k
  rw [Matrix.mul_apply]
  have key : ∀ n : Fin 16, qft4 j n * (star qft4 : Matrix (Fin 16) (Fin 16) ℂ) n k
      = (1 / 16 : ℂ) * (qftZeta ^ (j.val * n.val)
          * (starRingEnd ℂ) (qftZeta ^ (k.val * n.val))) := by
    intro n
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, qft4]
    norm_num
    ring
  rw [Finset.sum_congr rfl (fun n _ => key n), ← Finset.mul_sum, qft_sum]
  by_cases hjk : j = k <;> simp [hjk, Matrix.one_apply]

/-- Explicit form of unitarity: `Qᴴ * Q = 1` and `Q * Qᴴ = 1`. -/
theorem qft_conjTranspose_mul_self_and_self_mul :
    qft4ᴴ * qft4 = 1 ∧ qft4 * qft4ᴴ = 1 := by
  have h := qft_unitary_4
  rw [Matrix.mem_unitaryGroup_iff'] at h
  refine ⟨by simpa [Matrix.star_eq_conjTranspose] using h, ?_⟩
  simpa [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff.mp qft_unitary_4)

end QC

