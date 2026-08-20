import Mathlib

/-!
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
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

namespace Chem

/-- The set of probability vectors indexed by `ι`: nonnegative entries summing to `1`. -/

theorem convex_probVectors (ι : Type*) [Fintype ι] : Convex ℝ (probVectors ι) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  refine ⟨fun i => ?_, ?_⟩
  · simpa using add_nonneg (mul_nonneg ha (hx0 i)) (mul_nonneg hb (hy0 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx1, hy1]
    simpa using hab

/-- The Gibbs entropy is the sum of `negMulLog` over the coordinates. -/
