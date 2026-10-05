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

lemma symplecticForm_eq_dot {n : ℕ} (u v : Fin n × Fin 2 → ℝ) :
    symplecticForm u v = ∑ p : Fin n × Fin 2, jvec u p * v p := by
  rw [symplecticForm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h0 : jvec u (i, 0) = -u (i, 1) := by simp [jvec]
  have h1 : jvec u (i, 1) = u (i, 0) := by simp [jvec]
  rw [Fin.sum_univ_two, h0, h1]
  ring

