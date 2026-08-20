import Mathlib
/-!
# Higgs Mass Toy
Category: Frontier Physics
Target: Frontier.higgs_mass_toy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to be the first command in a file, so the header
-- module docstring above is placed immediately after the import.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The Mexican-hat scalar potential of the abelian Higgs toy model,
`V(φ) = lam * (|φ|² - v²)²`, written as a function of the modulus `r = |φ|`. -/
noncomputable def higgsPotential (lam v r : ℝ) : ℝ := lam * (r ^ 2 - v ^ 2) ^ 2

/-- Covariant derivative of a constant scalar field in a background gauge field:
`D φ = i g A φ` (the `∂φ` part vanishes for the constant vacuum configuration). -/
noncomputable def covDeriv (g A : ℝ) (phi : ℂ) : ℂ := Complex.I * (g * A : ℝ) * phi

/-- The squared mass acquired by the gauge boson, `m² = g² v²`. -/
noncomputable def gaugeMassSq (g v : ℝ) : ℝ := g ^ 2 * v ^ 2

/-- The scalar potential is nonnegative when the quartic coupling is positive. -/
theorem higgsPotential_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (v r : ℝ) :
    0 ≤ higgsPotential lam v r :=
  mul_nonneg hlam (sq_nonneg _)

/-- The potential vanishes on the vacuum manifold `|φ| = v`. -/
theorem higgsPotential_vacuum (lam v : ℝ) : higgsPotential lam v v = 0 := by
  simp [higgsPotential]

/-- The symmetric point `φ = 0` is not a minimum: it has strictly higher energy
than the broken vacuum. -/
theorem higgsPotential_zero_gt {lam v : ℝ} (hlam : 0 < lam) (hv : v ≠ 0) :
    higgsPotential lam v v < higgsPotential lam v 0 := by
  have : 0 < lam * (v ^ 2) ^ 2 := by positivity
  simpa [higgsPotential] using this

/-- The gauge-kinetic term evaluated on the vacuum configuration produces exactly a
mass term `m² A²` for the gauge field, with `m² = g² v²`. -/
theorem covDeriv_normSq {g v A : ℝ} {phi : ℂ} (hphi : ‖phi‖ = v) :
    ‖covDeriv g A phi‖ ^ 2 = gaugeMassSq g v * A ^ 2 := by
  have h : ‖covDeriv g A phi‖ = |g * A| * v := by
    simp [covDeriv, hphi]
  rw [h, gaugeMassSq]
  rw [mul_pow, sq_abs]
  ring

/-- **Abelian Higgs toy model: spontaneous symmetry breaking gives the gauge boson a mass.**

For a quartic coupling `lam > 0`, a nonzero vacuum expectation value `v > 0` and a nonzero
gauge coupling `g`:

* the Mexican-hat potential `V(r) = lam (r² - v²)²` is nonnegative and attains its minimum
  value `0` on the vacuum manifold `r = v`, while the symmetric point `r = 0` has strictly
  higher energy (so the `U(1)` symmetry is spontaneously broken);
* evaluating the gauge-covariant kinetic term on the vacuum configuration `‖φ‖ = v` yields
  precisely the mass term `m² A²`;
* the resulting gauge boson mass squared `m² = g² v²` is strictly positive.
-/
theorem higgs_mass_toy {lam v g : ℝ} (hlam : 0 < lam) (hv : 0 < v) (hg : g ≠ 0) :
    (higgsPotential lam v v = 0 ∧ ∀ r : ℝ, higgsPotential lam v v ≤ higgsPotential lam v r) ∧
      higgsPotential lam v v < higgsPotential lam v 0 ∧
      (∀ (A : ℝ) (phi : ℂ), ‖phi‖ = v →
        ‖covDeriv g A phi‖ ^ 2 = gaugeMassSq g v * A ^ 2) ∧
      0 < gaugeMassSq g v := by
  refine ⟨⟨higgsPotential_vacuum lam v, fun r => ?_⟩,
    higgsPotential_zero_gt hlam hv.ne', fun A phi hphi => covDeriv_normSq hphi, ?_⟩
  · rw [higgsPotential_vacuum]
    exact higgsPotential_nonneg hlam.le v r
  · have : (0:ℝ) < g ^ 2 * v ^ 2 := by positivity
    simpa [gaugeMassSq] using this

end Frontier

#print axioms Frontier.higgs_mass_toy

