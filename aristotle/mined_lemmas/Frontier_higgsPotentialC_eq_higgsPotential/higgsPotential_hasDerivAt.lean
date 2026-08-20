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

lemma higgsPotential_hasDerivAt (lam v r : ℝ) :
    HasDerivAt (higgsPotential lam v) (4 * lam * r * (r ^ 2 - v ^ 2)) r := by
  have h : HasDerivAt (fun x : ℝ => x ^ 2 - v ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).sub_const (v ^ 2)
  have h2 : HasDerivAt (fun x : ℝ => lam * (x ^ 2 - v ^ 2) ^ 2)
      (lam * (2 * (r ^ 2 - v ^ 2) ^ (2 - 1) * (2 * r))) r := (h.pow 2).const_mul lam
  refine h2.congr_deriv ?_
  simp
  ring

