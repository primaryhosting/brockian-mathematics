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

lemma hasDerivAt_gibbsWeight (β : ℝ) (H B : ι → ℝ) (i : ι) :
    HasDerivAt (fun l : ℝ => gibbsWeight β (fun j => H j - l * B j) i)
      (β * B i * gibbsWeight β H i) 0 := by
  have h1 : HasDerivAt (fun l : ℝ => -β * (H i - l * B i)) (β * B i) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const (B i)).const_sub (H i)).const_mul (-β)
    simpa using this
  have h2 := h1.exp
  simp only [gibbsWeight]
  simpa [mul_comm] using h2

omit [Nonempty ι] in
/-- Derivative of the perturbed partition function at zero coupling. -/
