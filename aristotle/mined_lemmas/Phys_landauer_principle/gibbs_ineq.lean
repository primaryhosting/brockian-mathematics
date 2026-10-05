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

theorem gibbs_ineq {α : Type*} [Fintype α] (p q : α → ℝ) (hp : IsProbDist p)
    (hq0 : ∀ a, 0 ≤ q a) (hqpos : ∀ a, p a ≠ 0 → 0 < q a) (hq1 : ∑ a, q a ≤ 1) :
    shannonEntropy p ≤ ∑ a, -(p a * Real.log (q a)) := by
  have key : ∀ a ∈ (univ : Finset α),
      p a * Real.log (q a) - p a * Real.log (p a) ≤ q a - p a := by
    intro a _
    rcases eq_or_lt_of_le (hp.nonneg a) with h | h
    · simp [← h, hq0 a]
    · have hqa : 0 < q a := hqpos a (ne_of_gt h)
      have hlog : Real.log (q a / p a) ≤ q a / p a - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hqa h)
      rw [Real.log_div (ne_of_gt hqa) (ne_of_gt h)] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt h)
      calc p a * Real.log (q a) - p a * Real.log (p a)
          = p a * (Real.log (q a) - Real.log (p a)) := by ring
        _ ≤ p a * (q a / p a - 1) := hmul
        _ = q a - p a := by field_simp
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hp.sum_one] at hsum
  have hA : ∑ a, -(p a * Real.log (p a)) = -∑ a, p a * Real.log (p a) := by simp
  have hB : ∑ a, -(p a * Real.log (q a)) = -∑ a, p a * Real.log (q a) := by simp
  rw [shannonEntropy, hA, hB]
  linarith

/-- Entropy of a product distribution is the sum of entropies. -/
