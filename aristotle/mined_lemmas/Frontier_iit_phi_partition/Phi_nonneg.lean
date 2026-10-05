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

/-!
## Setting

A *system* consists of a finite collection `ι` of binary elements.  A global state of the
system is a function `s : ι → Bool`.  The dynamics is given by a mechanism for each element:
`prob i s b` is the probability that element `i` takes the value `b` at the next time step,
given that the system is currently in state `s`.  Elements update independently given the
current global state, so the transition probability matrix of the whole system is the product
`tpm M s t = ∏ i, prob i s (t i)`.

Integrated information `Φ` is obtained by *cutting* the system along a bipartition
`(A, Aᶜ)`: the influence that each part receives from the other part is replaced by
independent noise (an average over the states of the other part).  The *effective information*
`ei M A` of a bipartition is the (state-averaged) `L¹` distance between the true transition
matrix and the transition matrix of the cut system, and `Φ` is the infimum of `ei M A` over
all bipartitions of the system.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite system of binary elements, each equipped with a stochastic mechanism
`prob i s : Bool → ℝ` giving the distribution of the next value of element `i` when the
system is currently in the global state `s`. -/
structure System (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- `prob i s b` is the probability that element `i` takes the value `b` at the next
  time step, given the current global state `s`. -/
  prob : ι → (ι → Bool) → Bool → ℝ
  prob_nonneg : ∀ (i : ι) (s : ι → Bool) (b : Bool), 0 ≤ prob i s b
  prob_sum : ∀ (i : ι) (s : ι → Bool), prob i s false + prob i s true = 1

/-- `mergeOn A s u` is the state that agrees with `s` on `A` and with `u` off `A`. -/

theorem Phi_nonneg (M : System ι) : 0 ≤ Phi M := by
  rcases Set.eq_empty_or_nonempty (ei M '' Bipartitions ι) with h | h
  · simp [Phi, h]
  · exact le_csInf h (by rintro x ⟨A, -, rfl⟩; exact ei_nonneg M A)

/-! ## The key computation: a part that is closed under the dynamics is unaffected by the cut -/

omit [Fintype ι] in
