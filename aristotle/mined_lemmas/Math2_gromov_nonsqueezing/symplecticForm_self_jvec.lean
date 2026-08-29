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

lemma symplecticForm_self_jvec {n : ℕ} (u : Fin n × Fin 2 → ℝ) :
    symplecticForm u (jvec u) = sqNorm u := by
  rw [sqNorm_eq, symplecticForm]
  refine Finset.sum_congr rfl fun i _ => by simp [jvec]; ring

