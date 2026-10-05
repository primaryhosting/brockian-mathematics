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

theorem higgs_mass_toy_real (lam g v : ℝ) (hlam : 0 < lam) (hg : 0 < g) (hv : 0 < v) :
    (higgsPotentialR lam v v = 0 ∧
        ∀ r : ℝ, higgsPotentialR lam v v ≤ higgsPotentialR lam v r) ∧
      (higgsPotentialR lam v (-v) = 0 ∧ (-v) ≠ v) ∧
      higgsPotentialR lam v v < higgsPotentialR lam v 0 ∧
      0 < gaugeBosonMassSqR g v ∧
      Real.sqrt (gaugeBosonMassSqR g v) = g * v := by
  have hVv : higgsPotentialR lam v v = 0 := by simp [higgsPotentialR]
  refine ⟨⟨hVv, ?_⟩, ⟨by simp [higgsPotentialR], by intro h; nlinarith⟩, ?_, ?_, ?_⟩
  · intro r
    rw [hVv]
    exact mul_nonneg hlam.le (sq_nonneg _)
  · rw [hVv]
    have h : higgsPotentialR lam v 0 = lam * v ^ 4 := by simp only [higgsPotentialR]; ring
    rw [h]
    positivity
  · unfold gaugeBosonMassSqR; positivity
  · unfold gaugeBosonMassSqR
    rw [show g ^ 2 * v ^ 2 = (g * v) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)

end Frontier

/-!
# Higgs Mass Toy
Category: Frontier Physics
Target: Frontier.higgs_mass_toy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (core Lean 4 only), so that the header comment above
is literally the first thing in the file.  The model parameters therefore live in `Int`,
which is a genuine special case of the abelian Higgs toy model: all statements below are
purely algebraic identities and inequalities in a commutative ordered ring.

A real-number version of the same statement, with the gauge boson mass expressed through
`Real.sqrt`, is proved in `RequestProject/HiggsMassToyReal.lean`
(`Frontier.higgs_mass_toy_real`).
-/

namespace Frontier

/-- Mexican-hat (symmetry breaking) potential of the abelian Higgs toy model, written as a
function of the modulus `r` of the complex scalar field:  `V(r) = lam * (r² - v²)²`. -/
