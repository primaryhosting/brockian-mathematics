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

/-- The Mexican-hat potential of the abelian Higgs toy model, written as a function of the
modulus `r = |φ|` of the complex scalar field:  `V(r) = lam * (r ^ 2 - v ^ 2) ^ 2`. -/

noncomputable def gaugeMass (g w : ℝ) : ℝ := g * w

/-- **Key intermediate lemma (spontaneous symmetry breaking).**
For a positive quartic coupling `lam` and a positive parameter `v`, the Mexican-hat potential
attains its minimum value `0` on the nonnegative moduli exactly at the nonzero value `r = v`;
in particular the symmetric configuration `r = 0` is *not* a minimum. -/
