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

lemma concaveOn_coord_negMulLog {ι : Type*} (i : ι) :
    ConcaveOn ℝ (nonnegOrthant ι) (fun p : ι → ℝ => Real.negMulLog (p i)) := by
  have h := Real.strictConcaveOn_negMulLog.concaveOn.comp_linearMap
    (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)
  refine h.subset (fun p hp => ?_) (convex_nonnegOrthant ι)
  exact hp i

/-- A finite sum of functions concave on a set is concave on that set. -/
