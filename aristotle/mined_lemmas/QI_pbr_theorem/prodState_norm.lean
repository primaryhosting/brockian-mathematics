/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
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

namespace QI

open MeasureTheory MeasureTheory.Measure Complex

noncomputable section

/-! ## The quantum input: the Pusey–Barrett–Rudolph measurement on two qubits -/

/-- The real number `1/√2`, viewed as a complex amplitude. -/

lemma prodState_norm (a b : Fin 2) : ‖prodState a b‖ = 1 := by
  fin_cases a <;> fin_cases b <;>
    · rw [EuclideanSpace.norm_eq]
      simp only [prodState, amp, idxL, idxR, Fin.sum_univ_four, WithLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.tail_cons, Matrix.cons_val_fin_one]
      norm_num [norm_rt_sq, mul_pow]

/-- The key quantum fact behind the PBR theorem: outcome `pairIdx a b` of the PBR measurement
has zero amplitude, hence zero Born probability, on the product preparation `|ψ_a⟩ ⊗ |ψ_b⟩`. -/
