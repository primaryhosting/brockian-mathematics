import Mathlib

/-!
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real

namespace Chem

/-- The Gibbs entropy of a probability vector `p`: `S(p) = -∑ i, p i * log (p i)`. -/
noncomputable def entropy {n : ℕ} (p : Fin n → ℝ) : ℝ := -∑ i, p i * Real.log (p i)

/-- The Gibbs entropy `-∑ i, p i * log (p i)` is a concave function of the probability
vector `p`, i.e. it is concave on the standard simplex of probability vectors. -/
theorem entropy_concave (n : ℕ) :
    ConcaveOn ℝ (stdSimplex ℝ (Fin n)) (entropy (n := n)) := by
  refine ⟨convex_stdSimplex ℝ (Fin n), ?_⟩
  intro p hp q hq a b ha hb hab
  have hnn : ∀ (r : Fin n → ℝ), r ∈ stdSimplex ℝ (Fin n) → ∀ i, 0 ≤ r i := fun r hr i => hr.1 i
  have key : ∀ i : Fin n,
      a • Real.negMulLog (p i) + b • Real.negMulLog (q i)
        ≤ Real.negMulLog (a • p i + b • q i) :=
    fun i => Real.strictConcaveOn_negMulLog.concaveOn.2 (hnn p hp i) (hnn q hq i) ha hb hab
  simp only [entropy, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  simp only [Real.negMulLog, smul_eq_mul, neg_mul, mul_neg, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  linarith [hsum]

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

