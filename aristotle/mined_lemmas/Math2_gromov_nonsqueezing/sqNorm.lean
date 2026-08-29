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

def sqNorm {n : ℕ} (v : Fin n × Fin 2 → ℝ) : ℝ := ∑ p : Fin n × Fin 2, (v p) ^ 2

/-- The open euclidean ball of radius `r` centred at the origin. -/
