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

lemma deriv_higgsPotential (r : ℝ) :
    deriv (fun x : ℝ => higgsPotential lam v x) r = 4 * lam * r * (r ^ 2 - v ^ 2) := by
  have h : (fun x : ℝ => higgsPotential lam v x)
      = fun x : ℝ => lam * (x ^ 2 - v ^ 2) ^ 2 := rfl
  rw [h]
  have : deriv (fun x : ℝ => lam * (x ^ 2 - v ^ 2) ^ 2) r
      = lam * deriv (fun x : ℝ => (x ^ 2 - v ^ 2) ^ 2) r := by
    apply deriv_const_mul
    fun_prop
  rw [this]
  have hd : HasDerivAt (fun x : ℝ => (x ^ 2 - v ^ 2) ^ 2) (2 * (r ^ 2 - v ^ 2) * (2 * r)) r := by
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2 - v ^ 2) (2 * r) r := by
      simpa using ((hasDerivAt_pow 2 r).sub_const (v ^ 2))
    simpa using h1.pow 2
  rw [hd.deriv]
  ring

/-- The vacuum is a stationary point of the potential. -/
