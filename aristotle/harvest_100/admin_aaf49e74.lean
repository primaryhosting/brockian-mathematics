import Mathlib

/-!
# Cnot Unitary Involutive
Category: Quantum Computing
Target: QC.cnot_unitary_involutive
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

/-- The CNOT gate as a `4 × 4` complex matrix (control = first qubit). -/
def cnot : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

open Matrix in
theorem cnot_unitary_involutive :
    cnotᴴ * cnot = 1 ∧ cnot * cnotᴴ = 1 ∧ cnot * cnot = 1 ∧ cnot ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have hH : cnotᴴ = cnot := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cnot, Matrix.conjTranspose_apply]
  have hmul : cnot * cnot = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cnot, Matrix.mul_apply, Fin.sum_univ_succ]
  refine ⟨by rw [hH]; exact hmul, by rw [hH]; exact hmul, hmul, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hH]
  exact hmul

end QC

