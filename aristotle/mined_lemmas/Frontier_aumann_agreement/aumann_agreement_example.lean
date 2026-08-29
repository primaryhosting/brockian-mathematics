import Mathlib

/-!
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
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

namespace Frontier

/-- The conditional probability of the event `E` given the (information) cell `C`,
computed from the weight function `p`. -/

theorem aumann_agreement_example :
    (∀ x, x ∈ exI₁ x) ∧ (∀ x y, y ∈ exI₁ x → exI₁ y = exI₁ x) ∧
    (∀ x, x ∈ exI₂ x) ∧ (∀ x y, y ∈ exI₂ x → exI₂ y = exI₂ x) ∧
    exI₁ 0 ≠ exI₂ 0 ∧
    (∀ x ∈ (Finset.univ : Finset (Fin 4)), 0 < ∑ y ∈ exI₁ x, exPrior y) ∧
    (∀ x ∈ (Finset.univ : Finset (Fin 4)), 0 < ∑ y ∈ exI₂ x, exPrior y) ∧
    (∀ x ∈ (Finset.univ : Finset (Fin 4)),
      condProb exPrior ({0, 2} : Finset (Fin 4)) (exI₁ x) = 1 / 2) ∧
    (∀ x ∈ (Finset.univ : Finset (Fin 4)),
      condProb exPrior ({0, 2} : Finset (Fin 4)) (exI₂ x) = 1 / 2) := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have e1 : ({0, 1} ∩ {0, 2} : Finset (Fin 4)) = {0} := by decide
  have e2 : ({2, 3} ∩ {0, 2} : Finset (Fin 4)) = {2} := by decide
  have e3 : ({0, 3} ∩ {0, 2} : Finset (Fin 4)) = {0} := by decide
  have e4 : ({1, 2} ∩ {0, 2} : Finset (Fin 4)) = {2} := by decide
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · intro x _
    fin_cases x
    · exact exPair_sum_pos h01
    · exact exPair_sum_pos h01
    · exact exPair_sum_pos h23
    · exact exPair_sum_pos h23
  · intro x _
    fin_cases x
    · exact exPair_sum_pos h03
    · exact exPair_sum_pos h12
    · exact exPair_sum_pos h12
    · exact exPair_sum_pos h03
  · intro x _
    fin_cases x
    · exact exPair_condProb h01 e1
    · exact exPair_condProb h01 e1
    · exact exPair_condProb h23 e2
    · exact exPair_condProb h23 e2
  · intro x _
    fin_cases x
    · exact exPair_condProb h03 e3
    · exact exPair_condProb h12 e4
    · exact exPair_condProb h12 e4
    · exact exPair_condProb h03 e3

end Frontier

