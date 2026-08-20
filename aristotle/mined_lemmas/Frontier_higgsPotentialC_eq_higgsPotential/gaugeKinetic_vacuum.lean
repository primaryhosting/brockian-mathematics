import Mathlib

/-!
# Higgs Mass Toy
Category: Frontier Physics
Target: Frontier.higgs_mass_toy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The "Mexican hat" scalar potential of the abelian Higgs model, written as a
function of the modulus `r = |φ|` of the complex scalar field:
`V(r) = lam * (r² - v²)²`. -/

lemma gaugeKinetic_vacuum (g v A : ℝ) :
    gaugeKinetic g A 0 ((v : ℝ) : ℂ) = gaugeMassSq g v * A ^ 2 := by
  have h : covD g A 0 ((v : ℝ) : ℂ) = Complex.I * (-((g * A * v : ℝ) : ℂ)) := by
    simp [covD]; ring
  simp only [gaugeKinetic, h, gaugeMassSq, norm_mul, Complex.norm_I, one_mul,
    norm_neg, Complex.norm_real, Real.norm_eq_abs]
  simp [mul_pow, sq_abs]
  ring

/-- At the symmetric point `φ = 0` no mass term is generated: the gauge field is massless. -/
