/-
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Finset

variable {Ω ι κ : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The information cell (element of the information partition) of an agent whose
information is described by the signal function `f`, at the state `ω`:
the set of states the agent cannot distinguish from `ω`. -/

theorem aumann_agreement_instance :
    (0 < ∑ _x ∈ (univ : Finset (Fin 4)), (1:ℝ)/4) ∧
    (∀ ω : Fin 4, 0 < ∑ _x ∈ cell sig₁ ω, (1:ℝ)/4) ∧
    (∀ ω : Fin 4, 0 < ∑ _x ∈ cell sig₂ ω, (1:ℝ)/4) ∧
    (∀ ω : Fin 4, (∑ x ∈ cell sig₁ ω, if x ∈ ({0, 2} : Finset (Fin 4)) then (1:ℝ)/4 else 0)
        / (∑ _x ∈ cell sig₁ ω, (1:ℝ)/4) = 1/2) ∧
    (∀ ω : Fin 4, (∑ x ∈ cell sig₂ ω, if x ∈ ({0, 2} : Finset (Fin 4)) then (1:ℝ)/4 else 0)
        / (∑ _x ∈ cell sig₂ ω, (1:ℝ)/4) = 1/2) := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · intro ω; fin_cases ω <;> norm_num (config := { decide := true }) [cell_sig₁]
  · intro ω; fin_cases ω <;> norm_num (config := { decide := true }) [cell_sig₂]
  · intro ω; fin_cases ω <;> norm_num (config := { decide := true }) [cell_sig₁]
  · intro ω; fin_cases ω <;> norm_num (config := { decide := true }) [cell_sig₂]

end Frontier

