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

lemma gaugeKinetic_gauge_invariant (g A theta : ℝ) (dphi phi : ℂ) :
    gaugeKinetic g A (Complex.exp (theta * Complex.I) * dphi)
      (Complex.exp (theta * Complex.I) * phi) = gaugeKinetic g A dphi phi := by
  have h : covD g A (Complex.exp (theta * Complex.I) * dphi)
      (Complex.exp (theta * Complex.I) * phi)
      = Complex.exp (theta * Complex.I) * covD g A dphi phi := by
    simp [covD]; ring
  simp [gaugeKinetic, h]

/-- The zero set of the potential is exactly the vacuum circle `|φ| = v`. -/
