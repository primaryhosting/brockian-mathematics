/-
# Hadamard Involutive
Category: Quantum Computing
Target: QC.hadamard_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hadamard Involutive
Category: Quantum Computing
Target: QC.hadamard_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix

/-- The single-qubit Hadamard gate `H = (1/√2) • !![1, 1; 1, -1]`. -/

lemma sq_inv_sqrt_two : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    have : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  field_simp
  linear_combination -h

/-- The Hadamard matrix is self-adjoint and squares to the identity. -/
