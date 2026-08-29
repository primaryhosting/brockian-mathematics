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

lemma pbr_inner_eq_zero (a b : Fin 2) :
    inner ℂ (pbrVec (pairIdx a b)) (prodState a b) = 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [pairIdx, pbrVec, prodState, amp, idxL, idxR, PiLp.inner_apply, Fin.sum_univ_four,
      conj_rt, rt_mul_rt]

/-! ## A measure-theoretic tool: monotonicity of product measures -/

/-- If `μ ≤ μ'` and `ν ≤ ν'` then `μ ⊗ ν ≤ μ' ⊗ ν'`. -/
