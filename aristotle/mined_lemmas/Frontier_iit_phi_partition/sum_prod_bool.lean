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

A *system* consists of a finite set `V` of binary nodes.  A (global) state of the
system is a function `s : V → Bool`.  The dynamics is given by a *mechanism*
`p : V → (V → Bool) → ℝ`, where `p v s` is the probability that node `v` is `true`
at the next time step, given that the current global state is `s`; the nodes are
updated independently of one another (conditionally on the current state).

Integrated information `Φ` at a state `s` is the minimum, over all bipartitions of
the system into two nonempty parts, of the *effective information* generated across
that partition: the Kullback–Leibler divergence between the true transition
distribution and the transition distribution obtained after *cutting* all the
connections that cross the partition (each cut input being replaced by independent
uniform noise).

The theorem `Frontier.iit_phi_partition` states that a *disconnected* system — one
admitting a bipartition into two nonempty parts that do not influence each other —
has `Φ = 0` in every state.
-/

variable {V : Type*}

/-- `nodeProb p v s b` is the probability that node `v` takes the boolean value `b`
at the next time step, given the current global state `s`. -/

theorem sum_prod_bool [Fintype V] [DecidableEq V] (g : V → Bool → ℝ) :
    ∑ t : V → Bool, ∏ v : V, g v (t v) = ∏ v : V, (g v true + g v false) := by
  have h : ∀ v : V, (g v true + g v false) = ∑ b : Bool, g v b := by
    intro v; simp
  simp_rw [h]
  rw [Finset.prod_univ_sum]
  congr 1

/-- The transition kernel of any mechanism is normalised. -/
