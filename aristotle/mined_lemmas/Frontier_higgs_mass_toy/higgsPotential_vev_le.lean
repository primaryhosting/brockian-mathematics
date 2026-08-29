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

lemma higgsPotential_vev_le (mu2 lam : ℝ) (hlam : 0 < lam) (φ : ℝ) :
    higgsPotential mu2 lam (vev mu2 lam) ≤ higgsPotential mu2 lam φ := by
  rcases le_or_gt mu2 0 with hmu | hmu
  · rw [vev_of_nonpos mu2 lam hmu]
    unfold higgsPotential
    nlinarith [sq_nonneg φ, sq_nonneg (φ ^ 2), mul_nonneg (neg_nonneg.mpr hmu) (sq_nonneg φ)]
  · have hv : vev mu2 lam ^ 2 = mu2 / (2 * lam) := vev_sq mu2 lam hlam hmu
    have hmu2 : mu2 = 2 * lam * vev mu2 lam ^ 2 := by
      rw [hv]; field_simp
    unfold higgsPotential
    nlinarith [sq_nonneg (φ ^ 2 - vev mu2 lam ^ 2), hlam.le]

/-- In the broken phase the gauge boson mass squared is `m_A² = g² μ² / (2λ)`. -/
