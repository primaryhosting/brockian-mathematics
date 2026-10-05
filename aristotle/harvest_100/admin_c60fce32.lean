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
def simplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

/-- The Gibbs entropy of a probability vector, `-∑ i, p i * log (p i)`. -/
noncomputable def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  -∑ i, p i * Real.log (p i)

lemma entropy_eq_sum_negMulLog {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    entropy p = ∑ i, Real.negMulLog (p i) := by
  simp [entropy, Real.negMulLog, Finset.sum_neg_distrib]

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
theorem entropy_concave (ι : Type*) [Fintype ι] :
    ConcaveOn ℝ (simplex ι) (entropy (ι := ι)) := by
  refine ⟨convex_simplex ι, ?_⟩
  rintro x ⟨hx0, -⟩ y ⟨hy0, -⟩ a b ha hb hab
  have key : ∀ i ∈ (Finset.univ : Finset ι),
      a • Real.negMulLog (x i) + b • Real.negMulLog (y i)
        ≤ Real.negMulLog (a • x i + b • y i) :=
    fun i _ => Real.strictConcaveOn_negMulLog.concaveOn.2 (hx0 i) (hy0 i) ha hb hab
  have := Finset.sum_le_sum key
  simpa [entropy_eq_sum_negMulLog, Finset.sum_add_distrib, Finset.smul_sum] using this

end Chem

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

