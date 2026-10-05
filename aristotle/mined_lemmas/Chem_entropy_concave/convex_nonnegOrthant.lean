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

lemma convex_nonnegOrthant (ι : Type*) : Convex ℝ (nonnegOrthant ι) := by
  intro x hx y hy a b ha hb _ i
  have := mul_nonneg ha (hx i)
  have := mul_nonneg hb (hy i)
  simpa using add_nonneg ‹0 ≤ a * x i› ‹0 ≤ b * y i›

/-- Each coordinate term `p ↦ negMulLog (p i)` is concave on the nonnegative orthant. -/
