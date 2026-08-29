/-
# Higgs Mass Toy
Category: Frontier Physics
Target: Frontier.higgs_mass_toy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The Mexican-hat potential of the abelian Higgs toy model,
`V(φ) = λ (φ² - v²)²`, with quartic coupling `λ` and symmetry-breaking scale `v`. -/
noncomputable def higgsPotential (lam v phi : ℝ) : ℝ := lam * (phi ^ 2 - v ^ 2) ^ 2

/-- The squared mass acquired by the abelian gauge boson from a scalar background
value `phi` with gauge coupling `g`, namely `m² = g² φ²`. -/
noncomputable def gaugeMassSq (g phi : ℝ) : ℝ := g ^ 2 * phi ^ 2

/-- **Abelian Higgs toy model: spontaneous symmetry breaking gives the gauge boson a mass.**

For positive quartic coupling `lam`, positive symmetry-breaking scale `v` and positive
gauge coupling `g`:

* the field value `φ = v` globally minimizes the Mexican-hat potential, and the minimum
  value is `0`;
* the symmetric configuration `φ = 0` is *not* a minimum (it has strictly higher energy),
  and there the gauge boson stays massless;
* in the broken vacuum `φ = v` the gauge boson acquires a strictly positive squared mass,
  whose square root is exactly `m = g v`. -/
theorem higgs_mass_toy (lam v g : ℝ) (hlam : 0 < lam) (hv : 0 < v) (hg : 0 < g) :
    (∀ phi : ℝ, higgsPotential lam v v ≤ higgsPotential lam v phi) ∧
      higgsPotential lam v v = 0 ∧
      higgsPotential lam v v < higgsPotential lam v 0 ∧
      gaugeMassSq g 0 = 0 ∧
      0 < gaugeMassSq g v ∧
      Real.sqrt (gaugeMassSq g v) = g * v := by
  have hVv : higgsPotential lam v v = 0 := by
    simp [higgsPotential]
  refine ⟨?_, hVv, ?_, ?_, ?_, ?_⟩
  · intro phi
    rw [hVv]
    have : (0:ℝ) ≤ (phi ^ 2 - v ^ 2) ^ 2 := sq_nonneg _
    simpa [higgsPotential] using mul_nonneg hlam.le this
  · rw [hVv, higgsPotential]
    have hv4 : 0 < v ^ 4 := by positivity
    nlinarith
  · simp [gaugeMassSq]
  · have : 0 < g ^ 2 * v ^ 2 := by positivity
    simpa [gaugeMassSq] using this
  · have hsq : gaugeMassSq g v = (g * v) ^ 2 := by
      simp [gaugeMassSq, mul_pow]
    rw [hsq, Real.sqrt_sq (by positivity)]

#print axioms Frontier.higgs_mass_toy

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

