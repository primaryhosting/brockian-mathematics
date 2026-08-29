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

noncomputable def higgsPotentialR (lam v r : ℝ) : ℝ := lam * (r ^ 2 - v ^ 2) ^ 2

/-- Squared mass acquired by the gauge boson through the Higgs mechanism, `m_A² = g² v²`. -/
