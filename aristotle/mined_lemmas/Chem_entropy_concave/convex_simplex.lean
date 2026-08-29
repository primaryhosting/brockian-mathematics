/-!
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Real Finset

/-- The probability simplex on a finite index type `ι`: vectors with nonnegative
entries summing to `1`. -/

lemma convex_simplex (ι : Type*) [Fintype ι] : Convex ℝ (simplex ι) := by
  rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · have := mul_nonneg ha (hx0 i)
    have := mul_nonneg hb (hy0 i)
    simpa using by positivity
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx1, hy1]
    simpa using hab

/-- **Concavity of the Gibbs entropy.**  The map `p ↦ -∑ i, p i * log (p i)` is a
concave function on the probability simplex. -/
