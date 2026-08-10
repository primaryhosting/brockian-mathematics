/-!
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Statement: The Gibbs entropy −Σ p_i log p_i is concave in the probability vector.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

/-- The Gibbs entropy of a probability vector `p`, `-∑ i, p i * log (p i)`. -/
noncomputable def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

lemma entropy_eq_neg_sum {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    entropy p = -∑ i, p i * Real.log (p i) := by
  simp [entropy, Real.negMulLog, Finset.sum_neg_distrib]

/-- The Gibbs entropy `-∑ pᵢ log pᵢ` is concave on the probability simplex. -/
theorem entropy_concave {ι : Type*} [Fintype ι] :
    ConcaveOn ℝ (stdSimplex ℝ ι) (entropy (ι := ι)) := by
  refine ⟨convex_stdSimplex ℝ ι, ?_⟩
  intro p hp q hq a b ha hb hab
  have hpi : ∀ i, (0:ℝ) ≤ p i := fun i => hp.1 i
  have hqi : ∀ i, (0:ℝ) ≤ q i := fun i => hq.1 i
  have key : ∀ i ∈ (Finset.univ : Finset ι),
      a • Real.negMulLog (p i) + b • Real.negMulLog (q i)
        ≤ Real.negMulLog (a • p i + b • q i) :=
    fun i _ => Real.concaveOn_negMulLog.2 (hpi i) (hqi i) ha hb hab
  have := Finset.sum_le_sum key
  simpa [entropy, Finset.sum_add_distrib, Finset.mul_sum] using this

end Chem

