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

theorem entropy_le_of_isProbDist (rho : B → ℝ) (hrho : IsProbDist rho) :
    shannonEntropy rho ≤ beta * (∑ b, rho b * E b) + Real.log (partitionFn E beta) := by
  have hg := gibbs_ineq rho (gibbsState E beta) hrho (fun b => (gibbsState_pos E beta b).le)
    (fun b _ => gibbsState_pos E beta b) (le_of_eq (gibbsState_isProbDist E beta).sum_one)
  refine hg.trans_eq ?_
  have h : ∀ b : B, -(rho b * Real.log (gibbsState E beta b))
      = rho b * (beta * E b) + rho b * Real.log (partitionFn E beta) := by
    intro b
    calc -(rho b * Real.log (gibbsState E beta b)) = rho b * -Real.log (gibbsState E beta b) := by
          ring
      _ = rho b * (beta * E b + Real.log (partitionFn E beta)) := by rw [neg_log_gibbsState]
      _ = _ := by ring
  simp only [h]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hrho.sum_one, one_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun b _ => by ring

end GibbsState

/-! ## Entropy of one bit, and of an erased bit -/

/-- One unbiased bit carries `log 2` nats of entropy. -/
