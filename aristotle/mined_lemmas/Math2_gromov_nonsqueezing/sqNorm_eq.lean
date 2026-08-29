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

lemma sqNorm_eq {n : ℕ} (v : Fin n × Fin 2 → ℝ) :
    sqNorm v = ∑ i : Fin n, ((v (i, 0)) ^ 2 + (v (i, 1)) ^ 2) := by
  simp [sqNorm, Fintype.sum_prod_type, Fin.sum_univ_two]

