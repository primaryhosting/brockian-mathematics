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

theorem mul_self_nonneg_int (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with ha | ha
  · exact Int.mul_nonneg ha ha
  · rw [← Int.neg_mul_neg]
    exact Int.mul_nonneg (Int.neg_nonneg.mpr ha) (Int.neg_nonneg.mpr ha)

/-- **Abelian Higgs toy model: spontaneous symmetry breaking gives the gauge boson a mass.**

For a positive quartic coupling `lam`, a positive gauge coupling `g` and a positive vacuum
expectation value `v`:

* `r = v` is a global minimum of the Mexican-hat potential, at which the potential vanishes;
* `r = -v` is a second, distinct global minimum: the vacuum is degenerate and the symmetry
  `r ↦ -r` (the residual `U(1)` phase rotation of the toy model) is spontaneously broken;
* the symmetric configuration `r = 0` is *not* a minimum, `V(v) < V(0)`;
* the gauge boson acquires a strictly positive mass `m_A = g v` with `m_A² = g² v²`.
-/
