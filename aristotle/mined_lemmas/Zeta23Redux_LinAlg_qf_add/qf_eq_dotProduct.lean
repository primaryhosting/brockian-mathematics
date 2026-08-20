import Mathlib

/-!
# Qf Add
Category: Linalg
Target: Zeta23Redux.LinAlg.qf_add
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace Zeta23Redux
namespace LinAlg

/-- The quadratic form associated to a complex matrix `M`, evaluated at a vector `x`
of Euclidean space: `qf M x = ∑ i, ∑ j, conj (x i) * M i j * x j`, i.e. `xᴴ M x`. -/

theorem qf_eq_dotProduct {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    qf M x = star x.ofLp ⬝ᵥ M.mulVec x.ofLp := by
  simp only [qf, dotProduct, Matrix.mulVec, Pi.star_apply, starRingEnd_apply,
    Finset.mul_sum, mul_assoc]

/-- Quadratic-form additivity: `qf (M + N) x = qf M x + qf N x`. -/
