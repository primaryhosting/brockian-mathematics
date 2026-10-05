/-
# Higgs Mass Toy
Category: Frontier Physics
Target: Frontier.higgs_mass_toy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Higgs Mass Toy
Category: Frontier Physics
Target: Frontier.higgs_mass_toy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The (real, radial) Higgs potential of the abelian Higgs toy model:
`V(φ) = -μ² φ² + λ φ⁴`, with quartic coupling `lam > 0`. -/

lemma vev_sq (mu2 lam : ℝ) (hlam : 0 < lam) (hmu : 0 < mu2) :
    vev mu2 lam ^ 2 = mu2 / (2 * lam) := by
  unfold vev
  rw [if_pos hmu, Real.sq_sqrt]
  positivity

/-- In the symmetric phase the vev vanishes. -/
