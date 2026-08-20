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

open Complex Finset

/-! ## The two-qubit vectors used in the PBR argument -/

/-- The normalisation constant `1/√2`. -/

theorem born_sum (a b : Fin 2) : ∑ i, bornProb i a b = 1 := by
  fin_cases a <;> fin_cases b <;>
    simp [bornProb, Fin.sum_univ_four, xi, prep, tens, ket0, ket1, ketP, ketM, expand,
      Complex.normSq_apply] <;> pbr_calc

/-- Sanity check: the probabilities are not all zero, e.g. outcome `1` on the
preparation `|0⟩ ⊗ |+⟩` has probability `1/4`. -/
