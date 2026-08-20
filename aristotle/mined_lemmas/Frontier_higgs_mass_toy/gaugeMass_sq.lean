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

/-- Mexican-hat (abelian Higgs) potential for a radial scalar field profile `r = |φ|`,
with quartic coupling `lam` and symmetry-breaking scale `v`:
`V(r) = lam * (r² - v²)²`. -/

lemma gaugeMass_sq (e r : ℝ) :
    gaugeMass e r ^ 2 = gaugeMassSq e r := by
  unfold gaugeMass gaugeMassSq
  rw [mul_pow, sq_abs]

/-- **Key intermediate lemma.** For a positive quartic coupling the Mexican-hat potential
is minimized exactly on the circle of vacua `r² = v²`: the value at `r = v` is a global
minimum, and any configuration attaining it has `r² = v²`. -/
