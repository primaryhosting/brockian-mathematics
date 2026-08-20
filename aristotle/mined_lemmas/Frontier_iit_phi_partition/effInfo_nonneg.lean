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

theorem effInfo_nonneg [Fintype V] [DecidableEq V] {p : V → (V → Bool) → ℝ}
    (hp : Stochastic p) (A : Finset V) (s : V → Bool) : 0 ≤ effInfo p A s := by
  have hq : Stochastic (cutProb p A) := fun v s => cutProb_mem_Ioo hp A v s
  have hsum1 : ∑ t : V → Bool, trans p s t = 1 := sum_trans_eq_one p s
  have hsum2 : ∑ t : V → Bool, trans (cutProb p A) s t = 1 := sum_trans_eq_one _ s
  have hpoint : ∀ t : V → Bool,
      trans p s t - trans (cutProb p A) s t
        ≤ trans p s t * Real.log (trans p s t / trans (cutProb p A) s t) := by
    intro t
    have h1 : 0 < trans p s t := trans_pos hp s t
    have h2 : 0 < trans (cutProb p A) s t := trans_pos hq s t
    have hlog : Real.log (trans (cutProb p A) s t / trans p s t)
        ≤ trans (cutProb p A) s t / trans p s t - 1 :=
      Real.log_le_sub_one_of_pos (div_pos h2 h1)
    have hneg : Real.log (trans (cutProb p A) s t / trans p s t)
        = -Real.log (trans p s t / trans (cutProb p A) s t) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [hneg] at hlog
    have hmul : trans p s t * (1 - trans (cutProb p A) s t / trans p s t)
        ≤ trans p s t * Real.log (trans p s t / trans (cutProb p A) s t) := by
      apply mul_le_mul_of_nonneg_left _ h1.le
      linarith
    have : trans p s t * (1 - trans (cutProb p A) s t / trans p s t)
        = trans p s t - trans (cutProb p A) s t := by
      field_simp
    linarith [this ▸ hmul]
  have := Finset.sum_le_sum (fun (t : V → Bool) (_ : t ∈ Finset.univ) => hpoint t)
  rw [Finset.sum_sub_distrib, hsum1, hsum2] at this
  simpa [effInfo] using this

/-! ## Disconnected systems have vanishing effective information across the split -/

/-- Across the splitting bipartition of a disconnected system, cutting the (absent)
crossing connections changes nothing. -/
