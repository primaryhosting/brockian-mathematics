/-
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset
open scoped Classical

namespace Phys

variable {X : Type*} [Fintype X]

/-- State visited by a path at (natural-number) time `n`, clamped to the horizon `N`. -/

lemma prod_detailedBalance (hDB : DetailedBalance β E p N) (γ : Fin (N + 1) → X) :
    (∏ t ∈ range N, p t (st γ t) (st γ (t + 1))) *
        Real.exp (-β * ∑ t ∈ range N, E (t + 1) (st γ t)) =
      (∏ t ∈ range N, p t (st γ (t + 1)) (st γ t)) *
        Real.exp (-β * ∑ t ∈ range N, E (t + 1) (st γ (t + 1))) := by
  rw [Finset.mul_sum, Finset.mul_sum, Real.exp_sum, Real.exp_sum, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun t ht => hDB t (Finset.mem_range.mp ht) _ _

/-- The reverse-process probability of the reversed trajectory, written in forward data. -/
