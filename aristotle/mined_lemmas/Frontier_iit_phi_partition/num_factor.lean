/-
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

namespace Frontier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The restriction of a global state `x` to the part `A` of the system. -/

lemma num_factor (h : DisconnectedAt f A) (a : ↥A → Bool) (b : ↥Aᶜ → Bool) :
    (∑ x : V → Bool, if restr A (f x) = a ∧ restr Aᶜ (f x) = b then (1 : ℝ) else 0)
      = cntA f A a * cntB f A b := by
  rw [sum_split A, cntA, cntB, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [restrA_indep f A h u v, restrB_indep f A h u v]
  by_cases h1 : restr A (f (joinState A u (fun _ => false))) = a <;>
    by_cases h2 : restr Aᶜ (f (joinState A (fun _ => false) v)) = b <;> simp [h1, h2]

