import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
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

namespace Phys

/-- Derivative of an exponentially decaying observable `t ↦ c e^{-a t}`. -/

lemma eq_corr_of_ode {f : ℝ → ℝ}
    (hf : ∀ t : ℝ, HasDerivAt f (-(S.relaxRate) * f t) t) (h0 : f 0 = 1 / (S.beta * S.k)) :
    f = S.corr := by
  have h := eq_expDecay_of_ode S.relaxRate hf
  rw [h0] at h
  exact h

end LangevinSystem

open LangevinSystem

/-- **Fluctuation–dissipation theorem** (classical, time domain).

For a system in thermal equilibrium at inverse temperature `beta`, the linear response
function `R` — the after-effect of an impulsive external force — is determined by the
spontaneous equilibrium fluctuations through

`R t = - beta * (d/dt) C t`,

where `C t = ⟪x(0) x(t)⟫` is the equilibrium autocorrelation function.  Dissipation
(the left-hand side) is thus rigidly tied to fluctuations (the right-hand side). -/
