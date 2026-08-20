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

This file formalizes Gromov's nonsqueezing phenomenon for **linear** symplectomorphisms
of `ℝ^(2n+2)`: a linear symplectic image of a ball of radius `r` that fits inside the
symplectic cylinder of radius `R` forces `r ≤ R`.  An affine version and a sharpness
statement are also proved.
-/

open scoped BigOperators
open Matrix

namespace Math2

/-- Bessel-type inequality for a pair of orthogonal vectors of equal length. -/

lemma dotProduct_J_mulVec_comm (u v : (l ⊕ l) → ℝ) :
    u ⬝ᵥ (Matrix.J l ℝ *ᵥ v) = -((Matrix.J l ℝ *ᵥ u) ⬝ᵥ v) := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.J_transpose, Matrix.neg_mulVec,
    neg_dotProduct]

/-- `J` is an isometry for the Euclidean inner product. -/
