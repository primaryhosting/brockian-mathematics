/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- A primitive `16`-th root of unity, `exp (2πi/16)`. -/
noncomputable def omega16 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The quantum Fourier transform matrix on 4 qubits: a `16 × 16` complex matrix with
entries `ω^(j k) / √16 = ω^(j k) / 4`, where `ω = exp (2πi/16)`. -/
noncomputable def qftMatrix4 : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun i j => omega16 ^ (i.val * j.val) / 4

lemma isPrimitiveRoot_omega16 : IsPrimitiveRoot omega16 16 := by
  have := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  simpa [omega16] using this

lemma omega16_ne_zero : omega16 ≠ 0 := isPrimitiveRoot_omega16.ne_zero (by norm_num)

lemma omega16_pow_pow_16 (n : ℕ) : (omega16 ^ n) ^ 16 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, isPrimitiveRoot_omega16.pow_eq_one, one_pow]

lemma norm_omega16 : ‖omega16‖ = 1 := by simp [omega16, Complex.norm_exp]

lemma star_omega16_pow (n : ℕ) : star (omega16 ^ n) = (omega16 ^ n)⁻¹ := by
  have h : star (omega16 ^ n) = (starRingEnd ℂ) (omega16 ^ n) := rfl
  rw [h, ← Complex.inv_eq_conj]
  simp [norm_omega16]

/-- Orthogonality relation for the `16`-th roots of unity. -/
lemma geom_sum_omega16 (i k : Fin 16) :
    ∑ j : Fin 16, (omega16 ^ i.val / omega16 ^ k.val) ^ j.val
      = if i = k then 16 else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (omega16 ^ i.val / omega16 ^ k.val) ^ j) 16]
  by_cases h : i = k
  · subst h
    rw [div_self (pow_ne_zero _ omega16_ne_zero)]
    simp
  · have hne : omega16 ^ k.val ≠ 0 := pow_ne_zero _ omega16_ne_zero
    have hz1 : omega16 ^ i.val / omega16 ^ k.val ≠ 1 := by
      intro hzz
      exact h (Fin.ext (isPrimitiveRoot_omega16.pow_inj i.isLt k.isLt
        (div_eq_one_iff_eq hne |>.mp hzz)))
    have hz16 : (omega16 ^ i.val / omega16 ^ k.val) ^ 16 = 1 := by
      rw [div_pow, omega16_pow_pow_16, omega16_pow_pow_16, div_one]
    rw [geom_sum_eq hz1, hz16]
    simp [h]

/-- The 4-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary_4 : qftMatrix4 ∈ Matrix.unitaryGroup (Fin 16) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i k
  rw [Matrix.mul_apply]
  have key : ∀ j : Fin 16, qftMatrix4 i j * (star qftMatrix4) j k
      = (omega16 ^ i.val / omega16 ^ k.val) ^ j.val / 16 := by
    intro j
    show omega16 ^ (i.val * j.val) / 4 * star (omega16 ^ (k.val * j.val) / 4) = _
    rw [star_div₀, star_omega16_pow, pow_mul, pow_mul, div_pow,
      show star (4 : ℂ) = 4 by norm_num]
    ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.sum_div, geom_sum_omega16]
  by_cases h : i = k <;> simp [h, Matrix.one_apply]

/-- Restatement: the conjugate transpose of the 4-qubit QFT matrix is its inverse. -/
theorem qft_conjTranspose_mul_self_4 : qftMatrix4.conjTranspose * qftMatrix4 = 1 :=
  (Matrix.mem_unitaryGroup_iff'.mp qft_unitary_4)

/-- The identification of the 4-qubit computational basis `Fin 4 → Fin 2` (bit strings)
with `Fin 16`, via binary expansion. -/
def qubits4Equiv : (Fin 4 → Fin 2) ≃ Fin 16 :=
  finFunctionFinEquiv.trans (finCongr (by norm_num))

/-- The 4-qubit QFT written directly on the tensor-product computational basis,
indexed by bit strings `Fin 4 → Fin 2`. -/
noncomputable def qftQubits4 : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ :=
  qftMatrix4.submatrix qubits4Equiv qubits4Equiv

/-- The 4-qubit QFT, indexed by the computational basis of bit strings, is unitary. -/
theorem qftQubits4_unitary :
    qftQubits4 ∈ Matrix.unitaryGroup (Fin 4 → Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hstar : star qftQubits4 = (star qftMatrix4).submatrix qubits4Equiv qubits4Equiv := by
    ext i j
    simp [qftQubits4, Matrix.star_apply]
  rw [hstar, qftQubits4, Matrix.submatrix_mul_equiv,
    Matrix.mem_unitaryGroup_iff.mp qft_unitary_4, Matrix.submatrix_one_equiv]

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

