import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Statement: Every bipartite pure state has a Schmidt decomposition with unique Schmidt coefficients.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ### Power sums determine a finite multiset of positive reals -/

open Polynomial in
/-- If two multisets of positive reals have the same power sums `∑ xᵏ` for every `k ≥ 1`,
they are equal. -/

lemma outer_apply {m : ℕ} (x y : EuclideanSpace ℂ (Fin m)) (j a : Fin m) :
    outer x y j a = x j * (starRingEnd ℂ) (y a) := rfl

