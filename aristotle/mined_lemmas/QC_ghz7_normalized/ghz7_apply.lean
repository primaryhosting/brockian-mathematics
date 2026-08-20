/-
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

/-- The state space of 7 qubits: the (finite-dimensional) complex Hilbert space with
orthonormal basis indexed by bit strings `Fin 7 → Bool`. -/
abbrev Qubits7 : Type := EuclideanSpace ℂ (Fin 7 → Bool)

/-- The computational basis vector `|b⟩` associated with a bit string `b : Fin 7 → Bool`. -/

lemma ghz7_apply (b : Fin 7 → Bool) :
    ghz7.ofLp b =
      if (∀ i, b i = false) ∨ (∀ i, b i = true) then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0 := by
  have h0 : (ket (fun _ => false)).ofLp b = if b = (fun _ => false) then (1 : ℂ) else 0 := by
    simp [ket, EuclideanSpace.single_apply]
  have h1 : (ket (fun _ => true)).ofLp b = if b = (fun _ => true) then (1 : ℂ) else 0 := by
    simp [ket, EuclideanSpace.single_apply]
  have hb0 : (b = fun _ => false) ↔ ∀ i, b i = false := funext_iff
  have hb1 : (b = fun _ => true) ↔ ∀ i, b i = true := funext_iff
  by_cases hc0 : ∀ i, b i = false
  · simp [ghz7, h0, h1, hb0, hb1, hc0]
  · by_cases hc1 : ∀ i, b i = true
    · simp [ghz7, h0, h1, hb0, hb1, hc1]
    · simp [ghz7, h0, h1, hb0, hb1, hc0, hc1]

/-- The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
