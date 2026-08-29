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

def symplecticForm {n : ℕ} (u v : Fin n × Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin n, (u (i, 0) * v (i, 1) - u (i, 1) * v (i, 0))

/-- The squared euclidean norm on `ℝ^{2n}`. -/
