import Mathlib

/-!
# Higgs Mass Toy (real-valued version)
Category: Frontier Physics
Target: Frontier.higgs_mass_toy_real
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Real-number companion of `Frontier.higgs_mass_toy` (see `RequestProject/HiggsMassToy.lean`,
which is import-free and therefore states the model over `Int`).
-/

namespace Frontier

/-- Mexican-hat potential of the abelian Higgs toy model as a function of the modulus
`r = |φ|` of the complex scalar field: `V(r) = lam * (r² - v²)²`. -/

noncomputable def gaugeBosonMassSqR (g v : ℝ) : ℝ := g ^ 2 * v ^ 2

/-- **Abelian Higgs toy model over the reals.**

For `lam, g, v > 0` the Mexican-hat potential is minimised on the degenerate vacuum
`r = ±v` (where it vanishes), the symmetric configuration `r = 0` is not a minimum, and the
gauge boson acquires the strictly positive mass `m_A = √(g² v²) = g v`. -/
