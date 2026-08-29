import Mathlib

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

/-
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

variable {ι : Type*} [Fintype ι]

/-- The Boltzmann weight `exp (-β (E i - λ A i))` of the microstate `i`, for the
Hamiltonian `E` perturbed by the field `λ` coupled to the observable `A`. -/

theorem susceptibility_nonneg [Nonempty ι] {beta : ℝ} (hbeta : 0 ≤ beta) (E A : ι → ℝ) :
    0 ≤ deriv (fun lam => expect beta E A lam A) 0 := by
  rw [(fluctuation_dissipation_variance beta E A).deriv]
  exact mul_nonneg hbeta
    (expect_nonneg beta E A 0 _ fun i => sq_nonneg (A i - expect beta E A 0 A))

end Phys

