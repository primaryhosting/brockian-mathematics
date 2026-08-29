/-
# Qft Unitary 2
Category: Quantum Computing
Target: QC.qft_unitary_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 2
Category: Quantum Computing
Target: QC.qft_unitary_2
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The 2-qubit quantum Fourier transform matrix: the `4 × 4` matrix with entries
`(1 / √4) * exp (2 π i j k / 4)`. -/
noncomputable def qft2 : Matrix (Fin 4) (Fin 4) ℂ :=
  fun j k => (1 / Real.sqrt 4 : ℝ) *
    Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / 4)

/-- Explicit form of the entries of `qft2`, using that the fourth root of unity
`exp (2 π i / 4)` is `i`. -/
lemma qft2_apply (j k : Fin 4) :
    qft2 j k = (1 / 2 : ℂ) * Complex.I ^ ((j : ℕ) * (k : ℕ)) := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hexp : Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / 4)
      = Complex.I ^ ((j : ℕ) * (k : ℕ)) := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * (k : ℕ)) / 4)
        = ((j : ℕ) * (k : ℕ) : ℕ) * (Real.pi * Complex.I / 2) by push_cast; ring,
      Complex.exp_nat_mul]
    congr 1
    rw [show ((Real.pi : ℂ) * Complex.I / 2) = (Real.pi / 2 : ℝ) * Complex.I by
        push_cast; ring, Complex.exp_mul_I]
    simp
  rw [qft2, hexp, h4]
  norm_num

/-- `qft2` is the familiar explicit 4×4 QFT matrix. -/
lemma qft2_eq_explicit :
    qft2 = (1 / 2 : ℂ) • !![1, 1, 1, 1;
                            1, Complex.I, -1, -Complex.I;
                            1, -1, 1, -1;
                            1, -Complex.I, -1, Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qft2_apply, pow_succ]

/-- `qft2ᴴ * qft2 = 1`. -/
lemma qft2_conjTranspose_mul_self : qft2ᴴ * qft2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qft2_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      pow_succ, Complex.ext_iff] <;> norm_num

/-- `qft2 * qft2ᴴ = 1`. -/
lemma qft2_mul_conjTranspose_self : qft2 * qft2ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qft2_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      pow_succ, Complex.ext_iff] <;> norm_num

/-- **The 2-qubit QFT matrix is unitary.** -/
theorem qft_unitary_2 : qft2 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  exact qft2_conjTranspose_mul_self

end QC

