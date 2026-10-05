/-!
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 7 → Bool)` whose basis is indexed by the `2^7` computational
basis states `|b₀ … b₆⟩`. -/
noncomputable def ghz7 : EuclideanSpace ℂ (Fin 7 → Bool) :=
  WithLp.toLp 2 (fun b =>
    if b = (fun _ => false) then (1 / Real.sqrt 2 : ℂ)
    else if b = (fun _ => true) then (1 / Real.sqrt 2 : ℂ)
    else 0)

/-- The 7-qubit GHZ state is a unit vector. -/
theorem ghz7_normalized : ‖ghz7‖ = 1 := by
  have hne : (fun _ => false : Fin 7 → Bool) ≠ (fun _ => true) := by
    intro h
    have := congrFun h 0
    simp at this
  have key : ∀ b : Fin 7 → Bool, ‖ghz7 b‖ ^ 2 =
      (if b = (fun _ => false) then (1 / 2 : ℝ) else 0) +
      (if b = (fun _ => true) then (1 / 2 : ℝ) else 0) := by
    intro b
    unfold ghz7
    by_cases h0 : b = (fun _ => false)
    · subst h0; simp [hne]
    · by_cases h1 : b = (fun _ => true)
      · subst h1; simp [Ne.symm hne]
      · simp [h0, h1]
  rw [EuclideanSpace.norm_eq]
  simp only [key]
  rw [Finset.sum_add_distrib]
  simp
  norm_num

end QC

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

