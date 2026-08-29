/-
# Higgs Mass Toy
Category: Frontier Physics
Target: Frontier.higgs_mass_toy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The "Mexican hat" scalar potential of the abelian Higgs toy model,
written in terms of the modulus `r = |φ|` of the complex scalar field:
`V(r) = lam * (r² - v²)²`. -/

lemma higgsPotential_strict_min (hlam : 0 < lam) (r : ℝ) (hr : r ^ 2 ≠ v ^ 2) :
    higgsPotential lam v v < higgsPotential lam v r := by
  rw [higgsPotential_vacuum]
  have h : (0:ℝ) < (r ^ 2 - v ^ 2) ^ 2 := by
    have : r ^ 2 - v ^ 2 ≠ 0 := sub_ne_zero_of_ne hr
    positivity
  exact mul_pos hlam h

