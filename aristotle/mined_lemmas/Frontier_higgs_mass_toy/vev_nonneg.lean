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

lemma vev_nonneg (mu2 lam : ℝ) : 0 ≤ vev mu2 lam := by
  unfold vev
  split
  · exact Real.sqrt_nonneg _
  · exact le_rfl

