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

/-- The probability of the (finite) event `S` under the weight function `p`. -/

lemma prob_inter_of_closed (hI : IsPartition I) (M : Finset Ω)
    (hclosed : ∀ ω ∈ M, I ω ⊆ M)
    (hq : ∀ ω ∈ M, prob p (E ∩ I ω) = q * prob p (I ω)) :
    prob p (E ∩ M) = q * prob p M :=
  prob_inter_of_closed_aux p I E q hI M.card M le_rfl hclosed hq

end Key

/-- **Aumann's agreement theorem** (finite state space, full-support common prior).

Two agents share a common prior `p` on a finite state space `Ω` and have information partitions
`I₁` and `I₂`.  At the state `ω₀` it is common knowledge (witnessed by the self-evident event `M`)
that agent 1's posterior probability of the event `E` is `q₁` and agent 2's posterior probability
of `E` is `q₂`.  Then `q₁ = q₂`: the agents cannot agree to disagree.

The hypothesis `hsum` (that the prior is normalised) is part of the statement that `p` is a common
prior, but it is not needed for the argument; only positivity of the prior is used. -/
