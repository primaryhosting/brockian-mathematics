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

theorem entropy_gibbsState :
    shannonEntropy (gibbsState E beta)
      = beta * (∑ b, gibbsState E beta b * E b) + Real.log (partitionFn E beta) := by
  have h : ∀ b : B, -(gibbsState E beta b * Real.log (gibbsState E beta b))
      = gibbsState E beta b * (beta * E b)
        + gibbsState E beta b * Real.log (partitionFn E beta) := by
    intro b
    calc -(gibbsState E beta b * Real.log (gibbsState E beta b))
        = gibbsState E beta b * -Real.log (gibbsState E beta b) := by ring
      _ = gibbsState E beta b * (beta * E b + Real.log (partitionFn E beta)) := by
          rw [neg_log_gibbsState]
      _ = _ := by ring
  rw [shannonEntropy]
  simp only [h]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, (gibbsState_isProbDist E beta).sum_one, one_mul,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun b _ => by ring

/-- Maximum-entropy property of the Gibbs state: any distribution has entropy at most
`beta * ⟨E⟩ + log Z`. -/
