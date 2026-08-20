/-
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

/-- The (first) Chern number of a Bloch band with Berry curvature `F` on the Brillouin-zone
torus `[0, 2π] × [0, 2π]`: the integral of the Berry curvature divided by `2π`. -/

theorem tknn_chern_hall_cos_modulated (e h : ℝ) (n : ℤ) (F : ℝ → ℝ → ℝ)
    (hF : ∀ kx ky : ℝ, F kx ky = ((n : ℝ) / (2 * Real.pi)) * (1 + Real.cos kx * Real.cos ky)) :
    chernNumber F = (n : ℝ) ∧ hallConductance e h F = (n : ℝ) * (e ^ 2 / h) :=
  tknn_of_flux e h n F (berryFlux_cos_modulated n F hF)

end Frontier

#print axioms Frontier.tknn_chern_hall
#print axioms Frontier.tknn_chern_hall_cos_modulated

