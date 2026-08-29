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

set_option grind.warning false

namespace Phys

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Boltzmann weight `e^{-β H(i)}` of the microstate `i`. -/

lemma hasDerivAt_partitionFn (β : ℝ) (H B : ι → ℝ) :
    HasDerivAt (fun l : ℝ => partitionFn β (fun j => H j - l * B j))
      (∑ i, β * B i * gibbsWeight β H i) 0 := by
  unfold partitionFn
  exact HasDerivAt.fun_sum (fun i _ => hasDerivAt_gibbsWeight β H B i)

omit [Nonempty ι] in
/-- Derivative of the (unnormalized) perturbed expectation value at zero coupling. -/
