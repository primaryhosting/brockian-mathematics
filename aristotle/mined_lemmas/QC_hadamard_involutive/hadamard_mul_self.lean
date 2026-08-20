import Mathlib

/-!
# Hadamard Involutive
Category: Quantum Computing
Target: QC.hadamard_involutive
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

/-- The single-qubit Hadamard gate `H = (1/√2) • !![1, 1; 1, -1]`, as a complex `2 × 2`
matrix. -/

theorem hadamard_mul_self : hadamard * hadamard = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    have h : ((Real.sqrt 2 : ℝ) ^ 2 : ℝ) = 2 := hs
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring_nf <;> rw [hsq]

/-- **Hadamard is involutive**: the Hadamard matrix satisfies `H† = H` and `H * H = I`. -/
