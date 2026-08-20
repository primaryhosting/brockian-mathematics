import Mathlib

/-!
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
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

/-- The Bekenstein bound expression `2 π k R E / (ℏ c)`: the maximal entropy that can be
contained in a region of radius `R` enclosing total energy `E`. -/

theorem bekenstein_bound
    {S k hbar c G R E : ℝ} (hhbar : 0 < hbar) (hc : 0 < c) (hG : 0 < G)
    (hR : R = schwarzschildRadius G c E)
    (hS : S ≤ bekensteinHawkingEntropy k hbar c G (sphereArea R)) :
    S ≤ 2 * Real.pi * k * R * E / (hbar * c) := by
  have h := bekensteinHawking_eq_bekensteinBoundValue (k := k) hhbar.ne' hc.ne' hG.ne' hR
  rw [h] at hS
  simpa [bekensteinBoundValue] using hS

end Phys

