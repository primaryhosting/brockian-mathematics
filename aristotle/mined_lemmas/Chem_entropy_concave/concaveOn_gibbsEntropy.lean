/-
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
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

namespace Chem

/-- The Gibbs entropy of a (finite) probability vector `p`, namely `- ∑ i, p i * log (p i)`,
written using `Real.negMulLog x = - x * log x`. -/

theorem concaveOn_gibbsEntropy (ι : Type*) [Fintype ι] :
    ConcaveOn ℝ (nonnegOrthant ι) (gibbsEntropy (ι := ι)) := by
  have := concaveOn_finset_sum (convex_nonnegOrthant ι) (Finset.univ : Finset ι)
    (fun i (p : ι → ℝ) => Real.negMulLog (p i))
    (fun i _ => concaveOn_coord_negMulLog i)
  simpa [gibbsEntropy] using this

/-- **The Gibbs entropy `-∑ pᵢ log pᵢ` is concave in the probability vector `p`.** -/
