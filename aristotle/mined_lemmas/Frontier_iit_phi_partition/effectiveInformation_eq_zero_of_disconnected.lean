/-
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A discrete (binary-node) dynamical system in the style of Integrated Information
Theory: a finite set `V` of nodes, each node `v` carrying a stochastic mechanism
`k v s : Bool → ℝ` giving the probability distribution of its next state given the
current global state `s : V → Bool`. -/
structure IITSystem (V : Type*) [Fintype V] where
  /-- `k v s b` is the probability that node `v` takes value `b` at the next step,
  given the current global state `s`. -/
  k : V → (V → Bool) → Bool → ℝ
  k_nonneg : ∀ v s b, 0 ≤ k v s b
  k_sum : ∀ v s, k v s true + k v s false = 1

/-- The transition probability matrix of the system: nodes update independently
(conditionally on the current global state), so the probability of moving from state
`s` to state `t` is the product of the individual node probabilities. -/

lemma effectiveInformation_eq_zero_of_disconnected (h : Disconnected S A) (s : V → Bool) :
    effectiveInformation S A s = 0 := by
  unfold effectiveInformation
  refine Finset.sum_eq_zero ?_
  intro t _
  rw [cutTpm_eq_tpm h s t, sub_self, abs_zero]

end Lemmas

/-- **Integrated information vanishes for a disconnected system.**

Given a finite binary-node stochastic system `S` and a bipartition `(A, Aᶜ)` into two
nonempty parts such that no node's mechanism depends on the other part, the integrated
information `Φ` (effective information minimized over all bipartitions) is zero. -/
