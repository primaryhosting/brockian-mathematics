/-
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Chem

/-- The Gibbs (Shannon) entropy of a probability vector `p : ι → ℝ`,
namely `-∑ i, p i * log (p i)`. -/
noncomputable def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  -∑ i, p i * Real.log (p i)

lemma entropy_eq_sum_negMulLog {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    entropy p = ∑ i, Real.negMulLog (p i) := by
  simp [entropy, Real.negMulLog, Finset.sum_neg_distrib]

/-- **Concavity of the Gibbs entropy.** The map `p ↦ -∑ i, p i * log (p i)` is concave
on the standard simplex of probability vectors.

The key ingredient is `Real.concaveOn_negMulLog`, the concavity of `x ↦ -x * log x`
on `[0, ∞)`. -/
theorem entropy_concave {ι : Type*} [Fintype ι] :
    ConcaveOn ℝ (stdSimplex ℝ ι) (entropy (ι := ι)) := by
  refine ⟨convex_stdSimplex ℝ ι, ?_⟩
  intro p hp q hq a b ha hb hab
  have key : ∀ i ∈ Finset.univ,
      a • Real.negMulLog (p i) + b • Real.negMulLog (q i)
        ≤ Real.negMulLog (a * p i + b * q i) := by
    intro i _
    exact Real.concaveOn_negMulLog.2 (Set.mem_Ici.2 (hp.1 i)) (Set.mem_Ici.2 (hq.1 i)) ha hb hab
  have hsum := Finset.sum_le_sum key
  simp only [entropy_eq_sum_negMulLog, smul_eq_mul, Finset.mul_sum, Pi.add_apply,
    Pi.smul_apply] at *
  rw [← Finset.sum_add_distrib]
  exact hsum

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

