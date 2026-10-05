/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Erasing one bit of information dissipates at least `k T log 2` of heat.

The setting formalised here is the standard statistical-mechanical derivation:

* the memory is a two-state system (`Bool`), initially in the uniform state
  (one bit of information, entropy `log 2`);
* the heat bath is a finite system with energies `E`, initially in the Gibbs
  state at inverse temperature `beta = 1 / (k T)`;
* system and bath are initially uncorrelated;
* the joint system is isolated, so its Shannon entropy does not decrease
  (in particular this holds, with equality, for reversible microscopic
  dynamics, i.e. for a bijection of the joint state space);
* the process is an *erasure*: the final marginal state of the memory is a
  point mass.

Then the heat `Q` absorbed by the bath is at least `k T log 2`.

The proof uses: invariance of Shannon entropy under relabelling, additivity on
product distributions, subadditivity (both consequences of Gibbs' inequality)
and the maximum-entropy property of the Gibbs state.
-/

namespace Phys

open Finset

/-- A probability distribution on a finite type. -/
structure IsProbDist {α : Type*} [Fintype α] (p : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ p a
  sum_one : ∑ a, p a = 1

/-- Shannon entropy (in nats) of a distribution on a finite type. -/

theorem shannonEntropy_prod {α β : Type*} [Fintype α] [Fintype β] (p : α → ℝ) (q : β → ℝ)
    (hp : IsProbDist p) (hq : IsProbDist q) :
    shannonEntropy (fun x : α × β => p x.1 * q x.2) = shannonEntropy p + shannonEntropy q := by
  have key : ∀ a : α, ∀ b : β, -(p a * q b * Real.log (p a * q b))
      = q b * -(p a * Real.log (p a)) + p a * -(q b * Real.log (q b)) := by
    intro a b
    rcases eq_or_ne (p a) 0 with h | h
    · simp [h]
    rcases eq_or_ne (q b) 0 with h' | h'
    · simp [h']
    rw [Real.log_mul h h']; ring
  have hinner : ∀ a : α, ∑ b, (q b * -(p a * Real.log (p a)) + p a * -(q b * Real.log (q b)))
      = -(p a * Real.log (p a)) + p a * shannonEntropy q := by
    intro a
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq.sum_one, one_mul]
    rfl
  rw [shannonEntropy, Fintype.sum_prod_type]
  simp only [key, hinner]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp.sum_one, one_mul]
  rfl

/-- Shannon entropy is invariant under relabelling of the state space. -/
