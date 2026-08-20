/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QI

/-! ### Two-qubit vectors, inner products and the states involved -/

/-- A (pure) qubit state vector. -/
abbrev Qubit := Fin 2 → ℂ

/-- A two-qubit state vector, written in curried form. -/
abbrev TwoQubit := Fin 2 → Fin 2 → ℂ

/-- The product (tensor) of two qubit vectors. -/

lemma pbr_born_sum_one (l₁ l₂ : Fin 2) :
    ∑ k, ‖ip (pbrBasis k) (tensor (st l₁) (st l₂))‖ ^ 2 = 1 := by
  fin_cases l₁ <;> fin_cases l₂ <;>
    simp [Fin.sum_univ_four, ip, pbrBasis, tensor, st, ket0, ketPlus, Fin.sum_univ_two,
      normsq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [s2_sq]

/-- The hypotheses of `pbr_theorem` are satisfiable, so the theorem is not vacuous:
the ψ-ontic model on two ontic states `Λ = Fin 2` (with `|0⟩` and `|+⟩` sitting on
the two different ontic states) satisfies all of them. -/
