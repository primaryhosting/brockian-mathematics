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

lemma gaugeMass_sq_of_pos (g mu2 lam : ℝ) (hlam : 0 < lam) (hmu : 0 < mu2) :
    gaugeMass g mu2 lam ^ 2 = g ^ 2 * mu2 / (2 * lam) := by
  rw [gaugeMass, mul_pow, vev_sq mu2 lam hlam hmu]
  ring

/-- **Abelian Higgs toy model.** For positive gauge coupling `g` and quartic coupling `λ`:

* the vacuum expectation value minimises the Higgs potential in either phase,
* the gauge boson acquires a strictly positive mass exactly when the symmetry is
  spontaneously broken, i.e. when `μ² > 0`; in the symmetric phase `μ² ≤ 0` it stays massless,
* and in the broken phase that mass is given by `m_A² = g² μ² / (2λ)`.
-/
