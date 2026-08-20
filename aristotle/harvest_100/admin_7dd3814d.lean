/-
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


import Mathlib

/-!
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
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

namespace QC

/-- The Pauli `X` matrix. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` matrix. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Hadamard matrix. -/
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / Real.sqrt 2 : ℝ) • !![1, 1; 1, -1]

/-- The Hadamard matrix equals `(X + Z)/√2`, and conjugating `X` by `H` yields `Z`. -/
theorem hadamard_XZ :
    H = ((1 : ℝ) / Real.sqrt 2 : ℝ) • (X + Z) ∧ H * X * H = Z := by
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  have hsq2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [pow_two, hsq]
  refine ⟨?_, ?_⟩
  · unfold H X Z
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · unfold H X Z
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ] <;>
      field_simp <;> ring_nf <;> simp only [hsq2]

end QC

#print axioms QC.hadamard_XZ

