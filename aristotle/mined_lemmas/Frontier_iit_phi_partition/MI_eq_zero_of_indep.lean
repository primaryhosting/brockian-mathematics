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

set_option grind.warning false

namespace Frontier

/-! ## Part 1: elementary finite information theory -/

/-- Kullback–Leibler divergence of `p` from `q`, over a finite alphabet.
With the `Real.log` conventions, terms with `p i = 0` contribute `0`. -/

theorem MI_eq_zero_of_indep {α β : Type*} [Fintype α] [Fintype β] (p : α → β → ℝ)
    (g : α → ℝ) (h : β → ℝ) (hfac : ∀ x y, p x y = g x * h y)
    (hg : ∑ x, g x = 1) (hh : ∑ y, h y = 1) : MI p = 0 := by
  have hm1 : ∀ x, (∑ y', p x y') = g x := by
    intro x; simp only [hfac, ← Finset.mul_sum, hh, mul_one]
  have hm2 : ∀ y, (∑ x', p x' y) = h y := by
    intro y; simp only [hfac, ← Finset.sum_mul, hg, one_mul]
  simp only [MI, hm1, hm2, ← hfac]
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
  rcases eq_or_ne (p x y) 0 with h0 | h0
  · simp [h0]
  · rw [div_self h0]; simp

/-! ## Part 2: discrete dynamical systems with a connectivity structure -/

/-- A finite system of binary nodes with stochastic, local dynamics.

* `E u v` means "node `v` receives input from node `u`";
* `f v s b` is the probability that node `v` is in state `b` at the next time step,
  given that the whole system is in state `s` now;
* `f_local` says the dynamics of `v` depends only on the states of its input nodes.
The nodes update independently given the current state, so the transition probability
of the whole system is the product of the `f v`. -/
structure System (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Connectivity: `E u v` means node `v` receives input from node `u`. -/
  E : V → V → Prop
  /-- `f v s b` is the probability that node `v` takes value `b` next, given current state `s`. -/
  f : V → (V → Bool) → Bool → ℝ
  /-- Probabilities are nonnegative. -/
  f_nonneg : ∀ v s b, 0 ≤ f v s b
  /-- Probabilities of the two possible next values of a node sum to one. -/
  f_sum : ∀ v s, f v s true + f v s false = 1
  /-- The dynamics of a node only depends on the current state of its input nodes. -/
  f_local : ∀ v s s', (∀ u, E u v → s u = s' u) → f v s = f v s'

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Combine a state of the part `A` and a state of its complement into a global state. -/
