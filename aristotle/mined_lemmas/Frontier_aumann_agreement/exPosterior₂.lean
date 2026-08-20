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

variable {Ω : Type*} [DecidableEq Ω]

/-- The prior probability of a (finite) event `S`, computed from the point masses `p`. -/

theorem exPosterior₂ : ∀ ω ∈ (univ : Finset (Fin 4)), 0 < prob exPrior (exI₂ ω) ∧
    prob exPrior (exE ∩ exI₂ ω) / prob exPrior (exI₂ ω) = 1/2 := by
  have c1 : (({0,3} : Finset (Fin 4)) ∩ {0,2}) = {0} := by decide
  have c2 : (({0,3} : Finset (Fin 4)) ∩ {1,3}) = {3} := by decide
  have d1 : (#({0,2} : Finset (Fin 4))) = 2 := by decide
  have d2 : (#({1,3} : Finset (Fin 4))) = 2 := by decide
  intro ω _
  fin_cases ω <;> norm_num [prob, exPrior, exI₂, exE, c1, c2, d1, d2]

/-- The hypotheses of `Frontier.aumann_agreement` are jointly satisfiable: applying the theorem
to the two agents above (with the whole state space as the common-knowledge event) is legitimate,
and indeed both posteriors equal `1/2`. -/
