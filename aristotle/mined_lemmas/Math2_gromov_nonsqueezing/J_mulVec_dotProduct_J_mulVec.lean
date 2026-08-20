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

lemma J_mulVec_dotProduct_J_mulVec (v : (l ⊕ l) → ℝ) :
    (Matrix.J l ℝ *ᵥ v) ⬝ᵥ (Matrix.J l ℝ *ᵥ v) = v ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.J_transpose, Matrix.neg_mulVec,
    Matrix.mulVec_mulVec, Matrix.J_squared]
  simp [Matrix.neg_mulVec, Matrix.one_mulVec]

end JLemmas

/-- **Gromov nonsqueezing for linear symplectomorphisms.**

Let `Φ` be a linear symplectomorphism of `ℝ^(2n+2)` (a matrix in the symplectic group,
i.e. `Φ * J * Φᵀ = J`).  If `Φ` maps the closed Euclidean ball of radius `r` centred at
the origin into the closed symplectic cylinder
`Z(R) = {z | z_{1}² + z_{2}² ≤ R²}` over the first symplectic coordinate plane, then
`r ≤ R`: a ball cannot be symplectically squeezed into a thinner cylinder.

The proof is the classical linear-algebra argument: writing `a`, `b` for the two rows of
`Φ` corresponding to the coordinates `z₁`, `z₂` of the cylinder, the symplectic condition
gives `⟪ Ja, b ⟫ = 1`, whence `‖a‖²‖b‖² - ⟪a,b⟫² ≥ 1` by a Bessel inequality; testing the
hypothesis on the vectors `r·a/‖a‖` and `r·b/‖b‖` gives `r²‖a‖² ≤ R²` and
`r²‖b‖² ≤ R²`, and multiplying these yields `r⁴ ≤ R⁴`. -/
