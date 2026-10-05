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

def cylinder {n : ℕ} (R : ℝ) : Set (Fin (n + 1) × Fin 2 → ℝ) :=
  {w | (w (0, 0)) ^ 2 + (w (0, 1)) ^ 2 < R ^ 2}

/-- A linear map is symplectic if it preserves the standard symplectic form. -/
