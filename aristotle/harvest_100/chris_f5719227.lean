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
def probVectors (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {p : ι → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

/-- The Gibbs entropy of a (probability) vector `p`, `S(p) = -∑ i, p i * log (p i)`. -/
noncomputable def gibbsEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  -∑ i, p i * Real.log (p i)

/-- The set of probability vectors is convex. -/
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
theorem gibbsEntropy_eq_sum {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    gibbsEntropy p = ∑ i, Real.negMulLog (p i) := by
  simp [gibbsEntropy, Real.negMulLog, Finset.sum_neg_distrib]

/-- **The Gibbs entropy `-∑ pᵢ log pᵢ` is concave in the probability vector.** -/
theorem entropy_concave (ι : Type*) [Fintype ι] :
    ConcaveOn ℝ (probVectors ι) (gibbsEntropy (ι := ι)) := by
  refine ⟨convex_probVectors ι, ?_⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0, -⟩ := hx
  obtain ⟨hy0, -⟩ := hy
  rw [gibbsEntropy_eq_sum, gibbsEntropy_eq_sum, gibbsEntropy_eq_sum]
  rw [smul_eq_mul, smul_eq_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := Real.concaveOn_negMulLog.2 (Set.mem_Ici.mpr (hx0 i)) (Set.mem_Ici.mpr (hy0 i))
    ha hb hab
  simpa using h

end Chem
