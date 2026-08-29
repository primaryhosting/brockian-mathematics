/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Math2

/-- The standard symplectic form on `ℝ^{2n}`, with coordinates indexed by
`Fin n × Fin 2` (the pair `(i, 0)`, `(i, 1)` being the `i`-th conjugate pair). -/

lemma symplecticForm_sq_le {n : ℕ} (u v : Fin n × Fin 2 → ℝ) :
    (symplecticForm u v) ^ 2 ≤ sqNorm u * sqNorm v := by
  rw [symplecticForm_eq_dot]
  calc (∑ p : Fin n × Fin 2, jvec u p * v p) ^ 2
      ≤ (∑ p : Fin n × Fin 2, (jvec u p) ^ 2) * ∑ p : Fin n × Fin 2, (v p) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = sqNorm u * sqNorm v := by rw [← sqNorm, ← sqNorm, sqNorm_jvec]

/-- Key quantitative step: if two vectors `p`, `q` control the two cylinder
coordinates and one of them has squared norm at least one, the ball cannot be
squeezed. -/
