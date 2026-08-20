/-
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Classical

namespace QC

/-- Computational basis states of 5 qubits are indexed by `Fin 5 → Bool`; the state space is
the Hilbert space `EuclideanSpace ℂ (Fin 5 → Bool)` (dimension `2^5 = 32`). -/
abbrev Qubits5 := EuclideanSpace ℂ (Fin 5 → Bool)

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`. -/

theorem ghz5_normalized : ‖ghz5‖ = 1 := by
  have hne : (fun _ => false : Fin 5 → Bool) ≠ (fun _ => true) := by
    intro h; have := congrFun h 0; simp at this
  rw [EuclideanSpace.norm_eq]
  have h : ∀ b : Fin 5 → Bool, ‖(ghz5 : Qubits5).ofLp b‖ ^ 2
      = (if b = (fun _ => false) then (1 / 2 : ℝ) else 0)
        + (if b = (fun _ => true) then (1 / 2 : ℝ) else 0) := by
    intro b
    simp only [ghz5, WithLp.ofLp_toLp]
    by_cases h0 : b = (fun _ => false)
    · subst h0; simp [hne]
    · by_cases h1 : b = (fun _ => true)
      · subst h1; simp [Ne.symm hne]
      · simp [h0, h1]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_true]
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

