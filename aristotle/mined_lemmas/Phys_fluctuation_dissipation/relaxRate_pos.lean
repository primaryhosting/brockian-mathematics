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

lemma relaxRate_pos : 0 < S.relaxRate := div_pos S.k_pos S.gamma_pos

/-- The equilibrium autocorrelation function `C t = ⟪x(0) x(t)⟫`.  In equilibrium the
position decays deterministically, `⟪x(0) x(t)⟫ = ⟪x(0)²⟫ e^{-(k/gamma) t}`, and
equipartition fixes the variance `⟪x²⟫ = 1 / (beta k)`. -/
