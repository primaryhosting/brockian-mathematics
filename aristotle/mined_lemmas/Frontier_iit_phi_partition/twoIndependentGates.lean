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

open Finset

/-!
## Setting

A *system* consists of a finite set `ι` of elements, each of which can be in one of
finitely many states `S`.  A global state of the system is a function `x : ι → S`.
The dynamics is given by a *mechanism*: for every element `i`, a conditional
probability `p i x s` that `i` will be in state `s` at the next time step, given that
the system is currently in the global state `x`.  Different elements are updated
independently, so the transition probability of the whole system is the product of
the individual mechanisms.
-/

/-- A finite discrete stochastic system: `p i x s` is the probability that element `i`
transitions to state `s` when the system is currently in global state `x`.
The mechanism is assumed strictly positive (every next state has positive
probability), which is the usual non-degeneracy assumption making the
Kullback–Leibler divergences below finite. -/
structure System (ι S : Type*) [Fintype ι] [DecidableEq ι] [Fintype S] where
  /-- `p i x s` = probability that element `i` is in state `s` at the next step. -/
  p : ι → (ι → S) → S → ℝ
  /-- Every transition has strictly positive probability. -/
  pos : ∀ i x s, 0 < p i x s
  /-- The mechanism of each element is a probability distribution on states. -/
  sum_one : ∀ i x, ∑ s, p i x s = 1

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S]

/-- The transition probability of the whole system: the probability of moving from
global state `x` to global state `y`. -/

noncomputable def twoIndependentGates : System Bool Bool where
  p := fun i x s => if x i = s then 3 / 4 else 1 / 4
  pos := by intro i x s; split <;> norm_num
  sum_one := by intro i x; rcases x i <;> simp <;> norm_num

