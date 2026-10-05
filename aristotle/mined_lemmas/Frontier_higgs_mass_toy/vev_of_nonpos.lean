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

lemma vev_of_nonpos (mu2 lam : ℝ) (hmu : mu2 ≤ 0) : vev mu2 lam = 0 := by
  unfold vev
  rw [if_neg (not_lt.mpr hmu)]

/-- The vev minimises the Higgs potential, in both phases. -/
