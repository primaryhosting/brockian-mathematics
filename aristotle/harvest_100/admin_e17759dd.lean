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
noncomputable def gaugeBosonMassSqR (g v : ℝ) : ℝ := g ^ 2 * v ^ 2

/-- **Abelian Higgs toy model over the reals.**

For `lam, g, v > 0` the Mexican-hat potential is minimised on the degenerate vacuum
`r = ±v` (where it vanishes), the symmetric configuration `r = 0` is not a minimum, and the
gauge boson acquires the strictly positive mass `m_A = √(g² v²) = g v`. -/
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
def higgsPotential (lam v r : Int) : Int := lam * ((r * r - v * v) * (r * r - v * v))

/-- Mass acquired by the abelian gauge boson through the Higgs mechanism, `m_A = g * v`,
where `v` is the vacuum expectation value of the modulus of the scalar field. -/
def gaugeBosonMass (g v : Int) : Int := g * v

/-- Squared gauge boson mass appearing in the quadratic part of the gauge kinetic term
after spontaneous symmetry breaking: `m_A² = g² v²`. -/
def gaugeBosonMassSq (g v : Int) : Int := (g * g) * (v * v)

/-- Squares are nonnegative. -/
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
theorem higgs_mass_toy (lam g v : Int) (hlam : 0 < lam) (hg : 0 < g) (hv : 0 < v) :
    (higgsPotential lam v v = 0 ∧ ∀ r : Int, higgsPotential lam v v ≤ higgsPotential lam v r) ∧
      (higgsPotential lam v (-v) = 0 ∧ (-v) ≠ v) ∧
      higgsPotential lam v v < higgsPotential lam v 0 ∧
      gaugeBosonMassSq g v = gaugeBosonMass g v * gaugeBosonMass g v ∧
      0 < gaugeBosonMass g v := by
  have hVv : higgsPotential lam v v = 0 := by simp [higgsPotential]
  refine ⟨⟨hVv, ?_⟩, ⟨?_, by omega⟩, ?_, ?_, Int.mul_pos hg hv⟩
  · -- `V(v) = 0` is a lower bound for `V`
    intro r
    rw [hVv]
    exact Int.mul_nonneg (Int.le_of_lt hlam) (mul_self_nonneg_int _)
  · -- the second vacuum `r = -v`
    show lam * ((-v * -v - v * v) * (-v * -v - v * v)) = 0
    rw [Int.neg_mul_neg]
    simp
  · -- the symmetric point `r = 0` sits strictly higher
    rw [hVv]
    show 0 < lam * ((0 * 0 - v * v) * (0 * 0 - v * v))
    have h : (0 * 0 - v * v) * ((0 : Int) * 0 - v * v) = (v * v) * (v * v) := by
      simp [Int.neg_mul_neg]
    rw [h]
    exact Int.mul_pos hlam (Int.mul_pos (Int.mul_pos hv hv) (Int.mul_pos hv hv))
  · -- `g² v² = (g v)²`
    show (g * g) * (v * v) = (g * v) * (g * v)
    simp [Int.mul_comm, Int.mul_left_comm]

end Frontier

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

