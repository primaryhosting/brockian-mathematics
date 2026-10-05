import Mathlib
/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
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

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Kato's adiabatic generator associated with a smooth family of spectral projections
`P` with derivative `P'`: `K(s) = [P'(s), P(s)] = P'(s)P(s) - P(s)P'(s)`. -/

lemma Uev_hasDerivAt (t : ℝ) :
    HasDerivAt Uev (Phys.adiabaticGen (fun _ => (0:ℂ)) Pj Pj' t * Uev t) t := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-(sigma3 * sigma1)) t
  have hgen : Phys.adiabaticGen (fun _ => (0:ℂ)) Pj Pj' t = -(sigma3 * sigma1) := by
    simp [Phys.adiabaticGen, katoGen_Pj]
  rw [hgen]
  exact h

