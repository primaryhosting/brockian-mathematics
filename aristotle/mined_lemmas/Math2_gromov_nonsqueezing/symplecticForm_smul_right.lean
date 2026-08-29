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

lemma symplecticForm_smul_right {n : ℕ} (c : ℝ) (u v : Fin n × Fin 2 → ℝ) :
    symplecticForm u (c • v) = c * symplecticForm u v := by
  simp only [symplecticForm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => by ring

