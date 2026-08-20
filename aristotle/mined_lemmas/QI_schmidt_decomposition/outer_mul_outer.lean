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

lemma outer_mul_outer {m : ℕ} (x y z w : EuclideanSpace ℂ (Fin m)) :
    outer x y * outer z w = (inner ℂ y z : ℂ) • outer x w := by
  ext j a
  simp [outer, Matrix.mul_apply, PiLp.inner_apply, RCLike.inner_apply, Finset.mul_sum,
    mul_comm, mul_left_comm]

