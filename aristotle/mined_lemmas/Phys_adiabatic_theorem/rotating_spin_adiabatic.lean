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

theorem rotating_spin_adiabatic (t : ℝ) (ht : 0 ≤ t) :
    Uev t psi0 ≠ 0 ∧ Pj t (Uev t psi0) = Uev t psi0 ∧
      Ham t (Uev t psi0) = (1 : ℂ) • (Uev t psi0) :=
  ⟨Uev_apply_ne_zero t,
    Phys.adiabatic_theorem Pj_proj Pj_hasDerivAt Pj'_continuous Ham_eig continuous_const
      Uev_hasDerivAt Uev_zero Pj_zero_psi0 ht⟩

end RotatingSpin

end Phys

