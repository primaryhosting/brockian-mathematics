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

lemma trace_outer {m : ℕ} (x y : EuclideanSpace ℂ (Fin m)) :
    Matrix.trace (outer x y) = (inner ℂ y x : ℂ) := by
  simp [outer, Matrix.trace, Matrix.diag, PiLp.inner_apply, RCLike.inner_apply]

/-- Coordinate form of orthonormality. -/
